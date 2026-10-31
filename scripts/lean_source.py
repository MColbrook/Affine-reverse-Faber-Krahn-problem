"""Small comment lexer and formatting tools for mathematical Lean source files."""
import re

def strip_comments(source):
    """Preserve layout and ordinary string literals while removing nested comments."""
    result, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if quoted:
            result.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                i += 1
                result.append(source[i])
            elif source[i] == '"':
                quoted = False
            i += 1
        elif depth:
            if source.startswith("/-", i):
                result.extend("  "); depth += 1; i += 2
            elif source.startswith("-/", i):
                result.extend("  "); depth -= 1; i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            result.extend("  "); depth = 1; i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                result.append(" "); i += 1
        else:
            if source[i] == '"':
                quoted = True
            result.append(source[i]); i += 1
    assert depth == 0, "Unclosed Lean block comment."
    return "".join(result)


def compact_challenge(source):
    """Fold statement headers and remove comments/blank lines; preserve proof layout.

    This is a formatting transform, not a proof or statement checker. The
    resulting source requires a new build, separate review and Comparator run.
    """
    code = strip_comments(source)

    def fold_header(match):
        header = match.group(0)
        assert '"' not in header, "Do not fold a header containing a string literal."
        return " ".join(header.split())

    # Stop at the current theorem's assignment, including direct term proofs.
    # Requiring `by` would swallow a term proof and later declarations.
    # Leave the original whitespace after `:=` untouched for Lean's layout.
    code = re.sub(r"(?ms)^theorem \w+.*? :=(?=\s|$)", fold_header, code)
    lines = [line.rstrip() for line in code.splitlines() if line.strip()]
    result = "\n".join(lines) + "\n"
    assert len(lines) <= 1000, "Challenge exceeds Palomar's 1,000 physical-line limit."
    assert len(result.encode("utf-8")) <= 100 * 1024, "Challenge exceeds 100 KiB."
    return result
