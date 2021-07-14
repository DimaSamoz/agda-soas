"""Utility functions used in the library."""


def num_to_ix(n):
  """Convert number to subscript character.

  Args:
      n (int): Single-digit number

  Returns:
      str: The Unicode subscript for the number.
  """
  return "₀₁₂₃₄₅₆₇₈₉"[n]

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
  """Delete parentesese from a string

  Args:
      s (str): String to delete parentheses from

  Returns:
      str: Input without any opening or closing parentheses.
  """
  return s.replace('(','').replace(')','')

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
  print("\n".join(ls))
  print()

# def ar_proj(n):
#   def ar_proj_aux(n):
#       if n == 0: return "new"
#       else: return "old " + wrap(ar_proj_aux(n-1))
#   return "ar " + wrap(ar_proj_aux(n))


def splitstrip(s, delim):
  """Split a string s on a delimiter d, stripping the resulting strings of leading or trailing whitespace.

  Args:
      s (str): String to split
      delim (str): Delimiter to split on.

  Returns:
      list[str]: String s split on delim, with all elements without any leading or trailing whitespace.
  """
  return [x.strip() for x in s.split(delim)]