"""i3-options: options for an i3 command line, for dmenu's dynamicoptions patch.

    i3-options [--spec FILE] [--half-life DAYS] TEXT
        prints the options for the input TEXT, one per line, best first
    i3-options ... --record COMMAND
        counts an executed command in the usage statistics
    i3-options ... --confirm COMMAND
        exit status 0 if COMMAND ends the i3 session (contains `exit`), else 1

TEXT is always the last argument, which is how `dmenu -dy CMD` calls CMD on
every change of its input (https://tools.suckless.org/dmenu/patches/dynamicoptions/).
A single argument is always taken as TEXT, even if it looks like an option.

Every option is a whole input line: TEXT with one more word, or with its
last, unfinished word completed. A whole line is what the patched dmenu needs:
it does no matching of its own, Tab replaces the whole input by the selected
option, and Return prints the selected option (Shift+Return prints the input
as typed; with no options, Return does too).

How the options are made:
  - If the last token of TEXT is finished (TEXT ends with a space, or with a
    token that needs none after it, such as `[` or a closed quote), every
    word that i3's grammar accepts next gives one option. Words are keywords
    and values: those i3 knows now (workspaces, outputs, marks, window
    classes, ...) and those used before.
  - Otherwise the unfinished end of TEXT is completed. A word qualifies if it
    contains what is typed; words equal to it come first, then words starting
    with it, then the others.
  - Within each of these groups the order is by previous usage of the word in
    that position (see below), then the grammar's order.
  - An option ends with a space when more can follow, so that after Tab the
    next list appears; keywords that must follow are added (`rename
    workspace `, `[class=`).
  - If TEXT is a complete command, it is itself an option. When its last
    token is finished, it is ranked among the next words by how often a
    command was ended at that point, ahead of words never used; while a word
    is being completed it comes last.
  - If TEXT is not valid i3 syntax but its end would be as one quoted value
    (`workspace next door`), that reading is the last option.
  - Otherwise TEXT is i3 syntax as i3 reads it: `;` and `,` end a command
    unless quoted, also inside an exec command.

Setup: keep i3-options (the launcher) and i3_options.py (this file) in one
directory, together with parser-specs/commands.spec from the i3 source of your
version (it is not installed with i3; ~/.local/share/i3-prompt/, --spec and
$I3_PROMPT_SPEC also work). The code is a module rather than part of the
launcher because Python caches the compiled form of modules only: compiling
this file takes longer than everything else it does per call. The cache is
written to __pycache__ in this directory, if that is writable.

Usage statistics: ~/.local/state/i3-prompt/usage.json, written only by
--record. Scores are kept per word and position: for a keyword, the grammar
state it was used in (`left` after `move` and `left` after `focus` are
counted apart, and so is ending the command there); for a value, its kind (workspace, output, exec command, ...),
whatever command it was used in. Whole commands are not stored. A use made a
time t ago counts as 2^(-t/H), and a score is the sum over the uses. The
half-life H is 14 days by default (--half-life DAYS or $I3_PROMPT_HALF_LIFE);
`inf` gives the plain count. Scores decayed below 0.01 are dropped at the next
--record, so something used once is forgotten after about 6.6 half-lives (93
days by default). H therefore sets two things at once: how strongly recent
uses outweigh old ones, and how long anything is remembered.

Limitations:
  - dmenu waits for this program on every keystroke. Where measured, a call
    took 25 to 30 ms (8 ms of that to start Python), and up to 40 ms when
    $I3SOCK is not set and i3-msg has to be run for i3's values.
  - Return runs the first option, complete or not: `move ` goes to i3 as it
    is, which answers with a parse error.
  - Keyword sets that i3 checks in its C handlers rather than in the grammar
    are supplied from two small tables below (OUTPUT_WORDS, LAYOUTS), copied
    from the user guide; other such sets are not completed.
  - Criteria values taken from open windows are offered as anchored, escaped
    regexes ("^XTerm$"); con_id and id get no window list.
  - Values containing a newline, and options longer than 2000 characters, are
    skipped (dmenu reads lines into a fixed buffer).
"""
import json
import os
import re
import sys
import time

WS = " \t\r\n"
FREE = ("string", "word", "number")
# Accepted by `focus output` / `move ... to output` besides output names (user guide, "Focusing containers").
OUTPUT_WORDS = ["left", "right", "up", "down", "current", "primary", "nonprimary", "next"]
# Accepted by `layout toggle` (user guide, "Manipulating layout").
LAYOUTS = ["split", "all", "tabbed", "stacking", "splitv", "splith"]
HALF_LIFE_DAYS = 14.0  # a guess at how fast habits change, not a measured value
FORGET = 0.01  # entries whose score has decayed below this are dropped
# Criteria whose value i3 treats as a PCRE regex (user guide, "List of commands").
REGEX_CRITERIA = ("class", "instance", "window_role", "title", "workspace", "machine", "con_mark")


# ---- grammar ----------------------------------------------------------------

def load(path):
    """Port of the first step of i3's generate-command-parser.pl.
    Returns {state: [(token, identifier, next_state, is_call)]}."""
    lines = []
    for raw in open(path, encoding="utf-8").read().split("\n"):
        if re.match(r"\s*(#|$)", raw):
            continue
        if re.match(r"\s+->", raw):  # continuation of the previous token definition
            lines[-1] += raw
        else:
            lines.append(raw)
    states, cur = {}, None
    for line in lines:
        m = re.match(r"state ([A-Z0-9_]+):$", line)
        if m:
            cur = m.group(1)
            states[cur] = []
            continue
        ident, tokens, action = re.match(r"\s*([a-z_]+\s*=\s*|)(.*?)->\s*(.*)", line).groups()
        ident = ident.split("=")[0].strip()
        call = action.startswith("call ")
        if not action:
            nxt = cur  # no action: stay in the current state
        elif call:
            m = re.search(r"; ([A-Z_]+)$", action)
            nxt = m.group(1) if m else "INITIAL"  # after a call: INITIAL unless stated
        else:
            nxt = action
        for tok in tokens.split(","):
            states[cur].append((tok.strip(), ident, nxt, call))
    return states


def literal(tok):
    return tok[1:-1] if tok.startswith("'") else None


def consume(tok, s, pos):
    """End position if `tok` matches s at pos (the rules of parse_command() in
    i3's src/commands_parser.c), else None."""
    lit = literal(tok)
    if lit is not None:
        # strncasecmp: case-insensitive prefix match, no word boundary required
        return pos + len(lit) if s[pos:pos + len(lit)].lower() == lit.lower() else None
    if tok == "number":
        m = re.match(r"[+-]?\d+", s[pos:])
        return pos + m.end() if m else None
    if tok in ("string", "word"):
        if s[pos:pos + 1] == '"':
            end = pos + 1
            while end < len(s) and s[end] != '"':
                end += 2 if s[end] == "\\" and end + 1 < len(s) else 1  # backslash escapes the next character
            if end == pos + 1 and end < len(s):
                return None  # "" is rejected by parse_string()
            return min(end + 1, len(s))  # unterminated: the cursor is inside the quotes
        stop = ",;\r\n" if tok == "string" else " \t],;\r\n"
        end = pos
        while end < len(s) and s[end] not in stop:
            end += 1
        return end if end > pos else None
    if tok == "end":
        # the terminating NUL is handled by the caller (end of input = still typing)
        return pos + 1 if s[pos:pos + 1] in (",", ";") else None
    raise ValueError(tok)


def expected(states, state):
    """Tokens acceptable in `state` as (owner_state, token, identifier, next_state, is_call).
    The empty literal '' (used once, in FULLSCREEN) always matches, so it is followed."""
    out = []
    for tok, ident, nxt, call in states[state]:
        if tok == "''":
            out += expected(states, nxt)
        else:
            out.append((state, tok, ident, nxt, call))
    return out


def unquote(piece):
    if not piece.startswith('"'):
        return piece.strip()
    body = piece[1:-1] if len(piece) > 1 and piece.endswith('"') else piece[1:]
    return re.sub(r'\\(["\\])', r"\1", body)


def kind_of(state, ident, vals):
    """Which pool of values a free token draws from; also the key of its usage counts."""
    if ident in ("workspace", "old_name") or state == "MOVE_WORKSPACE_NUMBER":
        return "workspace"
    if ident in ("output", "mark"):
        return ident
    if ident == "bar_id":
        return "bar"
    if state == "MODE":
        return "binding_mode"
    if ident == "toggle_mode":
        return "layout"
    if ident == "cvalue":
        return "criteria:" + vals.get("ctype", "")
    if state == "SWAP_ARGUMENT":
        return "swap:" + vals.get("mode", "")
    return "%s:%s" % (state, ident)


def closed_quote(piece):
    """Whether a token starting with a double quote also ends with its closing quote."""
    i = 1
    while i < len(piece) and piece[i] != '"':
        i += 2 if piece[i] == "\\" and i + 1 < len(piece) else 1
    return piece.startswith('"') and i == len(piece) - 1


class Walk:
    """Result of running the grammar over a text: where the parser stands at its end."""

    def __init__(self):
        self.state, self.pos = "INITIAL", 0
        self.vals = {}       # identifier -> value, like the parser's stack (cleared after a call)
        self.looped = set()  # optional words already given in the current state
        self.steps = []      # (state, token, text, kind) for every token matched
        self.points = []     # (position, state, vals, looped, previous token) wherever the parser stood before a token
        self.inside = None   # (token, identifier, next_state, is_call): a free token reaches the end of the text
        self.error = False


def walk(states, text):
    w = Walk()
    while True:
        while w.pos < len(text) and text[w.pos] in WS:
            w.pos += 1
        w.points.append((w.pos, w.state, dict(w.vals), set(w.looped), w.steps[-1][1] if w.steps else None))
        if w.pos == len(text):
            return w
        for tok, ident, nxt, call in states[w.state]:  # ordered choice: first matching token wins
            end = consume(tok, text, w.pos)
            if end is None:
                continue
            piece, lit = text[w.pos:end], literal(tok)
            w.steps.append((w.state, tok, piece, kind_of(w.state, ident, w.vals) if tok in FREE else None))
            if end == len(text) and tok in FREE:
                w.inside = (tok, ident, nxt, call)
                return w
            if ident:
                w.vals[ident] = lit if lit is not None else unquote(piece)
            if call or nxt == "INITIAL":
                w.vals = {}
            if nxt == w.state and not call and lit:
                w.looped.add(lit.strip())  # optional words are self-loops in the spec
            elif nxt != w.state:
                w.looped = set()
            w.state, w.pos = nxt, end
            break
        else:
            w.error = True
            return w


def may_end(states, state):
    return any(tok == "end" for _, tok, _, _, _ in expected(states, state))


END = "<end>"  # usage key for "the command ends here", counted like a keyword


def end_state(states, text):
    """The state whose `end` token the end of the text would match, if the
    text stops where a command may stop but could also go on; else None."""
    w = walk(states, text)
    if w.error or (w.inside is not None and not closed_quote(w.steps[-1][2]) and w.inside[0] == "string"):
        return None
    state = w.inside[2] if w.inside is not None else w.state
    owners = [owner for owner, tok, _, _, _ in expected(states, state) if tok == "end"]
    return owners[0] if owners and state != "INITIAL" else None


def is_complete(states, text):
    """Whether the text is a command that i3 would accept as it stands."""
    w = walk(states, text)
    if w.error or not w.steps:
        return False
    last = w.steps[-1]
    if w.inside:
        if last[2].startswith('"') and not closed_quote(last[2]):
            return False
        return w.inside[2] == "INITIAL" or may_end(states, w.inside[2])
    if w.state == "INITIAL":
        return last[1] not in ("end", "']'")  # not after a separator, and bare criteria do nothing
    return may_end(states, w.state)


# ---- live values and usage statistics ---------------------------------------

def output_of(argv, env, seconds=2.0):
    """stdout of a command, or b"" if it cannot run or takes too long.
    (subprocess would do, but importing it costs as much as a whole call.)"""
    import select
    try:
        r, w = os.pipe()
        pid = os.fork()
    except OSError:
        return b""
    if pid == 0:
        try:
            os.dup2(w, 1)
            os.dup2(os.open(os.devnull, os.O_WRONLY), 2)
            os.close(r)
            os.execvpe(argv[0], argv, env)
        finally:
            os._exit(127)
    os.close(w)
    chunks, deadline = [], time.monotonic() + seconds
    while True:
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([r], [], [], left)[0]:
            os.kill(pid, 9)  # dmenu is frozen while it waits for us
            chunks = []
            break
        chunk = os.read(r, 65536)
        if not chunk:
            break
        chunks.append(chunk)
    os.close(r)
    os.waitpid(pid, 0)
    return b"".join(chunks)


# Message types of i3's IPC protocol (include/i3/ipc.h).
IPC_TYPES = {"get_workspaces": 1, "get_outputs": 3, "get_tree": 4, "get_marks": 5,
             "get_bar_config": 6, "get_binding_modes": 8}


class I3:
    """What i3 knows now (workspaces, outputs, ...), asked only when a value is needed.

    The first list of a prompt needs all six answers. Six runs of i3-msg take
    longer than everything else in a call, so the answers are read from i3's IPC
    socket when $I3SOCK names it (i3 sets that for the programs it starts), and
    through `i3-msg -t` otherwise or if the socket fails (after a restart of i3
    the variable can be stale).
    """

    def __init__(self):
        self.cache = {}
        self.sock = False  # False: not tried yet; None: not available

    def get(self, msgtype):
        if msgtype not in self.cache:
            raw = self.ipc(msgtype)
            if raw is None:
                # without $I3SOCK, which i3-msg would trust as well: it then asks the X server for the path
                env = {k: v for k, v in os.environ.items() if k != "I3SOCK"}
                raw = output_of(["i3-msg", "-t", msgtype], env)
            try:
                self.cache[msgtype] = json.loads(raw.decode("utf-8", "replace"))
            except ValueError:
                self.cache[msgtype] = []
        return self.cache[msgtype]

    def ipc(self, msgtype):
        """The reply over the IPC socket, or None if that way is not available."""
        if self.sock is None:
            return None
        try:
            import struct
            if self.sock is False:
                # _socket is the C module under `socket`; importing `socket`
                # itself takes longer than the queries it would save.
                import _socket
                self.sock = _socket.socket(_socket.AF_UNIX, _socket.SOCK_STREAM)
                self.sock.settimeout(2.0)
                self.sock.connect(os.environ["I3SOCK"])
            self.sock.sendall(struct.pack("=6sII", b"i3-ipc", 0, IPC_TYPES[msgtype]))
            _, size, _ = struct.unpack("=6sII", self.read(14))
            return self.read(size)
        except (ImportError, KeyError, OSError, ValueError):
            self.sock = None
            return None

    def read(self, size):
        data = b""
        while len(data) < size:
            chunk = self.sock.recv(size - len(data))
            if not chunk:
                raise OSError("i3 closed the connection")
            data += chunk
        return data

    def windows(self):
        todo, out = [self.get("get_tree")], []
        while todo:
            node = todo.pop()
            if isinstance(node, dict):
                if node.get("window"):
                    out.append(node)
                todo += node.get("nodes", []) + node.get("floating_nodes", [])
        return out


def live_values(kind, state, i3):
    """(values currently known to i3 for this kind, whether nothing else can be valid)."""
    if kind == "workspace":
        return [w["name"] for w in i3.get("get_workspaces")], False
    if kind == "output":
        return OUTPUT_WORDS + [o["name"] for o in i3.get("get_outputs") if o.get("active")], True
    if kind == "mark":
        return list(i3.get("get_marks")), state != "MARK"  # `mark` takes a new name, the others an existing one
    if kind == "swap:mark":
        return list(i3.get("get_marks")), True
    if kind == "bar":
        return list(i3.get("get_bar_config")), True
    if kind == "binding_mode":
        return list(i3.get("get_binding_modes")), True
    if kind == "layout":
        return LAYOUTS, True
    if kind.startswith("criteria:"):
        ctype = kind.split(":", 1)[1]
        if ctype == "urgent":
            return ["latest", "oldest"], True
        if ctype == "con_id":
            return ["__focused__"], False
        if ctype == "con_mark":
            raw = list(i3.get("get_marks"))
        elif ctype == "workspace":
            raw = [w["name"] for w in i3.get("get_workspaces")]
        elif ctype == "window_type":
            raw = [n.get("window_type") for n in i3.windows()]
        else:
            raw = [(n.get("window_properties") or {}).get(ctype) for n in i3.windows()]
        raw = [v for v in dict.fromkeys(raw) if isinstance(v, str) and v and "\n" not in v]
        if ctype in REGEX_CRITERIA:
            # anchored and escaped: an unanchored "1" would also match workspace "10"
            raw = ["^" + re.sub(r"([\\^$.|?*+()\[\]{}])", r"\\\1", v) + "$" for v in raw]
        focused = ["__focused__"] if ctype in ("class", "instance", "window_role", "title", "workspace") else []
        return focused + raw, False
    return [], False


def written(value, tok, state, states):
    """The value as it has to be typed for i3 to read it back as this token: quoted unless safe."""
    if tok == "number":
        return value
    safe = r"[\w.:+@/-]+( [\w.:+@/-]+)*" if tok == "string" else r"[\w.:+@/-]+"
    # Tokens tried earlier in this state would take the text first (a workspace
    # called "next", or "nextfoo": literals match as prefixes).
    earlier = []
    for t, _, _, _ in states[state]:
        if t == tok:
            break
        earlier.append(t)
    shadowed = any(consume(t, value + " ", 0) is not None for t in earlier)
    return quote(value) if shadowed or not re.fullmatch(safe, value) else value


def quote(value):
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def stats_path():
    base = os.environ.get("XDG_STATE_HOME") or os.path.expanduser("~/.local/state")
    return os.path.join(base, "i3-prompt", "usage.json")


class Usage:
    """Usage scores with exponential decay.

    A use at time t contributes 2^(-(now - t) / H) to the score of its entry.
    The sum over all uses is stored as [score, time of the last update]; this
    loses nothing, since decay multiplies every term of the sum by the same
    factor. H -> infinity is the plain count. There is no useful H -> 0 limit:
    the order tends to "latest use first", but entries are dropped once below
    FORGET, so only the last few commands would be remembered at all. A
    half-life changed later applies to the stored sums as they are (the terms
    are not kept, so they cannot be re-weighted).
    """

    def __init__(self, half_life_days):
        self.half_life = half_life_days * 86400.0
        self.now = time.time()
        self.data = self.load()

    def load(self):
        data = {"tokens": {}, "values": {}}
        try:
            with open(stats_path(), encoding="utf-8") as f:
                raw = json.load(f)
            written_at = os.path.getmtime(stats_path())
            for part in data:
                for bucket, items in raw.get(part, {}).items():
                    for key, entry in items.items():
                        # A bare number is a count from the first version of this
                        # script, which kept no times: dated by the file itself.
                        score, when = entry if isinstance(entry, list) else (entry, written_at)
                        data[part].setdefault(bucket, {})[key] = [float(score), float(when)]
        except (OSError, ValueError, AttributeError, TypeError):
            return {"tokens": {}, "values": {}}  # missing or damaged file: start over
        return data

    def decayed(self, entry):
        score, when = entry
        # max(): a clock that was set back must not inflate the score
        return score * 0.5 ** (max(0.0, self.now - when) / self.half_life)

    def score(self, part, bucket, key):
        entry = self.data[part].get(bucket, {}).get(key)
        return self.decayed(entry) if entry else 0.0

    def known(self, part, bucket):
        """Keys of a bucket, highest score first."""
        return sorted(self.data[part].get(bucket, {}), key=lambda key: -self.score(part, bucket, key))

    def record(self, states, command):
        """Adds one use, now, for each keyword and value of an executed command."""
        uses = []
        for state, tok, piece, kind in walk(states, command).steps:
            lit = literal(tok)
            if lit is not None and lit.strip():
                uses.append(("tokens", state, lit.strip()))
            elif tok in FREE:
                uses.append(("values", kind, unquote(piece)))
            elif tok == "end":
                uses.append(("tokens", state, END))  # the command was ended here by `;` or `,`
        state = end_state(states, command)
        if state is not None:
            uses.append(("tokens", state, END))  # ... or by the end of the line
        for part, bucket, key in uses:
            self.data[part].setdefault(bucket, {})[key] = [self.score(part, bucket, key) + 1.0, self.now]
        kept = {part: {bucket: {key: [round(e[0], 4), round(e[1])] for key, e in items.items()
                                if self.decayed(e) >= FORGET}
                       for bucket, items in buckets.items()}
                for part, buckets in self.data.items()}
        kept = {part: {bucket: items for bucket, items in buckets.items() if items} for part, buckets in kept.items()}
        path = stats_path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        text = json.dumps(kept, indent=1, sort_keys=True, ensure_ascii=False)
        text = re.sub(r"\[\s+([-+.\de]+),\s+(\d+)\s+\]", r"[\1, \2]", text)  # one entry per line, for reading by eye
        with open(path + ".tmp", "w", encoding="utf-8") as f:
            f.write(text + "\n")
        os.replace(path + ".tmp", path)  # atomic: a concurrent prompt never reads half a file


# ---- options ---------------------------------------------------------------

def join(head, word):
    """Appends a word to what is already typed; spacing only affects looks."""
    if word in ("=", "]", '"'):
        return head.rstrip() + word
    if head == "" or head[-1] in WS or head[-1] in "[=":
        return head + word
    return head + " " + word


def settle(states, option):
    """The option as it should stand in the input after Tab: with the keywords
    that must follow, and with a trailing space if anything else can follow."""
    while True:
        probe = option if option[-1:] in ("[", "=") else option + " "
        w = walk(states, probe)
        if w.error:
            return None
        if w.inside:
            return option  # an unquoted string runs to the end of the command: nothing can follow
        if w.state == "INITIAL" and w.steps[-1][1] not in ("end", "']'"):
            return option  # the command is complete
        follow = [(literal(tok), tok) for _, tok, _, _, _ in expected(states, w.state)]
        follow = [(lit, tok) for lit, tok in follow if lit is None or lit.strip() not in w.looped]
        if len(follow) == 1 and follow[0][0] is not None:
            # forced: `=` after a criterion, `show` after scratchpad, the closing quote of floating_from="user"
            option = join(probe, follow[0][0].strip())
            continue
        return probe if any(tok != "end" for _, tok in follow) else option


def tier(word, fragment):
    """0 equal to the fragment, 1 starting with it, 2 containing it, None
    otherwise; case is ignored, as in i3's keywords."""
    c, f = word.lower(), fragment.lower()
    if f and c == f.rstrip():
        return 0
    if c.startswith(f):
        return 1
    return 2 if f in c else None


def candidates(states, point, text, fragment, usage, i3):
    """Options that put one word in place of `fragment`, typed at a point where
    the parser stood, as (tier, -score, option)."""
    pos, state, vals, looped, previous = point
    if state == "INITIAL" and previous not in (None, "end", "']'"):
        # Right after a complete command, with no `;` or `,`. The grammar accepts
        # the next command there (`exit move left`); offering it is noise.
        return []
    head, found = text[:pos], []
    value_fragment = unquote(fragment) if fragment.startswith('"') else fragment
    for owner, tok, ident, nxt, call in expected(states, state):
        lit = literal(tok)
        if tok == "end":
            continue
        if lit is not None:
            lit = lit.strip()
            if lit == '"' or lit in looped:
                continue  # the quote of floating_from="auto" is noise; optional words are offered once
            t = tier(lit, fragment)
            if t is not None:
                found.append((t, -usage.score("tokens", owner, lit), join(head, lit)))
            continue
        kind = kind_of(owner, ident, vals)
        values, exhaustive = live_values(kind, owner, i3)
        if not exhaustive:
            values = values + usage.known("values", kind)  # values used before
        if owner in ("WORKSPACE_NUMBER", "MOVE_WORKSPACE_NUMBER"):
            values = [v for v in values if v[:1].isdigit()]  # i3's handler rejects a name without a leading number
        for value in dict.fromkeys(values):
            t = tier(value, value_fragment)
            if t is not None and "\n" not in value:
                found.append((t, -usage.score("values", kind, value), join(head, written(value, tok, owner, states))))
    return found


def options(states, text, usage, i3):
    w = walk(states, text)
    spaced = text == "" or text[-1] in WS
    found = []
    # Next word: the last token is finished (a space, or a token that needs none after it).
    closed = w.inside is not None and closed_quote(w.steps[-1][2])
    ahead = not w.error and (closed or (w.inside is None and (spaced or text[-1] in "[=];,")))
    complete = is_complete(states, text)
    if ahead:
        if complete:
            # Stopping here is ranked like a next word, ahead of unused ones.
            state = end_state(states, text)
            found.append((1, -usage.score("tokens", state, END) if state else 0.0, text.strip()))
        point = walk(states, text + " ").points[-1] if closed else w.points[-1]
        found += candidates(states, (len(text),) + point[1:], text, "", usage, i3)
    # Unfinished word: the rest of the line from any point where the parser
    # stood at a token boundary. An unquoted string may contain spaces, so a
    # trailing space does not finish it.
    if text and (not spaced or w.inside is not None):
        for point in reversed(w.points):
            pos = point[0]
            if pos < len(text) and (pos == 0 or text[pos - 1] in WS or text[pos - 1] in '[=];,"'):
                found += candidates(states, point, text, text[pos:], usage, i3)
    out = [option for _, _, option in sorted(found, key=lambda f: f[:2])]  # stable: ties keep the grammar's order
    out = [option if option == text.strip() and complete else settle(states, option) for option in out]
    if complete and not ahead:
        out.append(text.strip())
    elif w.error:
        # The text as one quoted value, where a value is possible: a workspace
        # called "next door" otherwise reads as the keyword `next` plus rubbish.
        for pos, state, _, _, _ in reversed(w.points):
            rest = text[pos:].strip()
            if rest and not rest.startswith('"') and any(tok in ("string", "word") for _, tok, _, _, _ in expected(states, state)):
                if is_complete(states, text[:pos] + quote(rest)):
                    out.append(text[:pos] + quote(rest))
                    break
    seen, result = set(), []
    if ahead and not complete:
        seen.add(text.strip())  # the input itself adds nothing when what can follow it is listed
    for option in out:
        if option is not None and option.strip() not in seen and len(option) <= 2000:
            seen.add(option.strip())
            result.append(option)
    return result


def find_spec(explicit):
    here = os.path.dirname(os.path.realpath(__file__))  # the launcher's directory as well
    data = os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share")
    places = [explicit or os.environ.get("I3_PROMPT_SPEC"), os.path.join(here, "commands.spec"),
              os.path.join(data, "i3-prompt", "commands.spec"), "/usr/share/i3-prompt/commands.spec"]
    for path in places:
        if path and os.path.isfile(path):
            return path
    fail("commands.spec not found; take parser-specs/commands.spec from the i3 source "
         "of your version and put it next to this script or in %s" % os.path.join(data, "i3-prompt"))


def fail(message):
    # stderr only: this runs on every keystroke, a dialog per call would be worse than no options
    print("i3-options: " + message, file=sys.stderr)
    sys.exit(2)


def main(argv):
    if not argv:
        fail("usage: i3-options [--spec FILE] [--half-life DAYS] [--record | --confirm] TEXT")
    # i3 commands are UTF-8 whatever the locale says
    text = os.fsencode(argv[-1]).decode("utf-8", "replace")
    flags, mode = argv[:-1], "options"
    opts = {"--spec": None, "--half-life": os.environ.get("I3_PROMPT_HALF_LIFE") or str(HALF_LIFE_DAYS)}
    while flags:
        flag = flags.pop(0)
        if flag in ("--record", "--confirm"):
            mode = flag
        elif flag in opts and flags:
            opts[flag] = flags.pop(0)
        else:
            fail("unknown option %r" % flag)
    try:
        half_life = float(opts["--half-life"])
    except ValueError:
        half_life = 0.0
    if not half_life > 0:  # also rejects nan
        fail("--half-life takes a positive number of days, or inf; got %r" % opts["--half-life"])
    states = load(find_spec(opts["--spec"]))
    if mode == "--confirm":
        # Return picks the first option, and `ex` already matches exit.
        return 0 if any(step[:2] == ("INITIAL", "'exit'") for step in walk(states, text).steps) else 1
    usage = Usage(half_life)
    if mode == "--record":
        usage.record(states, text.strip())
        return 0
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stdout.write("".join(option + "\n" for option in options(states, text, usage, I3())))
    return 0
