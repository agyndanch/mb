# GPT-5
import io
import re
import difflib
from typing import TextIO

_RE_BLOCK = re.compile(r"\$re:\s*(.*?)\s*\$", re.DOTALL)

def _template_to_regex(template_text: str) -> re.Pattern:
    """
    Convert a template with $re: ...$ blocks into a compiled regex that matches the entire text.
    Literal text is escaped; $re: ...$ content is inserted verbatim (as a non-capturing group).
    """
    parts = []
    pos = 0
    for m in _RE_BLOCK.finditer(template_text):
        # literal segment before this $re:...$
        literal = template_text[pos:m.start()]
        parts.append(re.escape(literal))
        # the regex block (insert as non-capturing group)
        parts.append(f"(?:{m.group(1)})")
        pos = m.end()
    # trailing literal
    parts.append(re.escape(template_text[pos:]))

    pattern = r"\A" + "".join(parts) + r"\Z"
    return re.compile(pattern, re.DOTALL)

def compare_output_with_template(
    template_filename: str,
    actual_file: TextIO,
    verbose: bool = False
) -> bool:
    """
    Compare actual output (from an open file object) to a template file.

    Template syntax:
      - Everything is taken literally
      - Except blocks of the form: $re: <regex here>$
        (the regex inside is inserted verbatim)

    Returns:
      True if the entire actual output matches the template; False otherwise.

    If verbose=True and there is a mismatch, prints a human-friendly message,
    including a small unified diff against a “rendered” view of the template
    (with regex blocks replaced by <RE:...> placeholders) to help debugging.

    Example template:
        abc.$re: \d{5}$
        total: $re:\s*\d+\s*$
    """
    with open(template_filename, "r", encoding="utf-8") as f:
        template_text = f.read()

    # Read the actual output
    actual_text = actual_file.read()

    # Compile regex from template
    rx = _template_to_regex(template_text)

    if rx.fullmatch(actual_text):
        return True

    if verbose:
        # Build a “rendered template” that is easier to read in a diff:
        # replace each $re: ...$ with a visible placeholder.
        rendered_template = _RE_BLOCK.sub(lambda m: f"<RE:{m.group(1)}>", template_text)

        # Show a compact unified diff to give context, even though the template has regex parts.
        diff = "".join(
            difflib.unified_diff(
                rendered_template.splitlines(keepends=True),
                actual_text.splitlines(keepends=True),
                fromfile="expected(template)",
                tofile="actual",
            )
        ) or "(no line-oriented diff available)"

        # Also print the compiled regex pattern and a short prefix of the actual text
        #print("Mismatch: actual output does not match the template.\n")
        #print("=== Compiled regex (anchors \\A..\\Z, DOTALL) ===")
        #print(rx.pattern)
        #print("\n=== Unified diff (template with <RE:...> placeholders vs actual) ===")
        print(diff)
        # Helpful preview
        def _preview(s: str, n=300):
            s = s.replace("\t", "\\t")
            return (s[:n] + ("…[truncated]" if len(s) > n else ""))
        print("\n=== Actual (prefix) ===")
        print(_preview(actual_text))

    return False
