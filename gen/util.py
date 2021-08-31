"""Utility functions used in the library."""


def num_to_ix(n):
  """Convert number to subscript character.

  Args:
      n (int): Single-digit number

  Returns:
      str: The Unicode subscript for the number.
  """
  return "₀₁₂₃₄₅₆₇₈₉"[n]

def num_to_uix(n):
  """Convert number to subscript character.

  Args:
      n (int): Single-digit number

  Returns:
      str: The Unicode superscript for the letter at the number.
  """
  return "ᵃᵇᶜᵈᵉᶠᵍʰⁱ"[n]


def num_to_frak(n):
  """Convert a number to a Fraktur character.

  Args:
      n (int): Number
  """
  return "𝔞𝔟𝔠𝔡𝔢𝔣𝔤𝔥𝔦𝔧𝔨𝔩𝔪𝔫𝔬𝔭𝔮𝔯𝔰𝔱𝔲𝔳𝔴𝔵𝔶𝔷"[n]

def wrap(s, sep=" "):
  """Wrap a string in parentheses if it contains an occurrence of sep.

  Args:
      s (string): String to possibly wrap in parentheses
      sep (str, optional): Separator whose presence indicates that the string must be wrapped. Defaults to " ".

  Returns:
      str: The string s wrapped in parentheses if it includes sep.
  """
  if sep in s: return "(" + s + ")"
  else: return s

def appn(s1, s2):
  """Append two strings, adding a space between them if either is nonempty.

  Args:
      s1 (str): The first string
      s2 (str): The second string

  Returns:
      str: The two strings concatenated and separated by a space.
  """
  if not s1: return s2
  elif not s2: return s1
  else: return s1 + " " + s2

def new_vars(n):
  """Output a list of n characters startin with 'a'

  Args:
      n (int): Number of characters to output

  Returns:
      list[str]: A list ['a', 'b', 'c', ...] of length n.
  """
  return [chr(ord('a') + i) for i in range(n)]

def no_parens(s):
  """Delete parenteses from a string

  Args:
      s (str): String to delete parentheses from

  Returns:
      str: Input without any opening or closing parentheses.
  """
  return s.replace('(','').replace(')','')

def strip_parens(s):
  """Strip parentheses around string"""
  if not s:
      return s
  if s[0] == "(" and s[-1] == ")":
      return strip_parens(s[1:-1])
  else:
      return s


def flatten(xss):
  """Flatten a list of lists

  Args:
      xss (list[list[T]]): A list of lists.

  Returns:
      list[T]: A flattened input.
  """
  return [x for xs in xss for x in xs]

def printl(ls):
  """Print a list of strings separated by newlines.

  Args:
      ls (list[str]): List of strings to print
  """
  print("\n".join([str(x) for x in ls]))
  print()

# def ar_proj(n):
#   def ar_proj_aux(n):
#       if n == 0: return "new"
#       else: return "old " + wrap(ar_proj_aux(n-1))
#   return "ar " + wrap(ar_proj_aux(n))


def splitstrip(s, delim=" "):
  """Split a string s on a delimiter d, stripping the resulting strings of leading or trailing whitespace.

  Args:
      s (str): String to split
      delim (str): Delimiter to split on.

  Returns:
      list[str]: String s split on delim, with all elements without any leading or trailing whitespace.
  """
  return [x.strip() for x in s.split(delim)]

def split_spaces(s):
  """Split a string at multiple (1 <) spaces.

  Args:
      s (string): Input string with more than one space between parts
  """
  cs = s.strip().split("  ")
  return [c.strip() for c in cs if c != ""]

def unzip(ts):
  return ([a for a, _ in ts], [b for _, b in ts])

def split_tuple(s):
  """Split a string of comma-separated expressions at the top level, 
  respecting parentheses and brackets:
  e.g. 'a, b, c(d, e), f' -> ['a', 'b', 'c(d, e)', 'f']

  Args:
      s (string): a string of comma-separated expressions which may themselves contain commas

  Returns:
      list(str): a list of top-level expressions
  """
  bl = 0  # Bracketing level
  ls = []
  w = ""
  for i, c in enumerate(s):

      if c in "[(":
          bl += 1
      elif c in ")]":
          bl -= 1
      if c == "," and not bl: # Add running word to the list as long as we're outside of brackets
          ls.append(w.strip())
          w = ""
      else:
          w += c # Add character to running string
  ls.append(w.strip())
  return ls

def fill_underscores(s, args):
  """Replace underscores in a string with elements of a list."""
  l = ""
  args.reverse()
  for c in s:
      if c == "_":
          a = args.pop()
          l += " " + a + " "
      else:
          l += c
  return l.strip()

def apply_replacements(s, ren_dict):
    """Replace occurrences of keys with values in a string"""
    for k, v in ren_dict.items():
        s = s.replace(k,v)
    return s

"""Higher order predicates"""
def forall(l, p):
    return all([p(x) for x in l])
def exists(l, p):
    return any([p(x) for x in l])
def any_in(l, s):
    return any([w in s for w in l])
def all_in(l,s):
    return all([w in s for w in l])


def list_union(l1, l2):
    """Union of lists, avoiding duplicates"""
    return list(dict.fromkeys(l1 + l2))

"""Padding operations"""
def lpad(s, n):
    return " " * (n - len(s)) + s

def rpad(s, n):
    return s + " " * (n - len(s))

def cpad(s, n):
    p = (n - len(s)) // 2
    return p * " " + s + (p) * " "
