#!/usr/bin/env python3
import argparse
from string import Template
import os
from os import path
from pathlib import Path, PurePath
from collections import OrderedDict
from typing import Type
from gen.type import *
from gen.term import *
from gen.eq import *

class Syntax:
  """Second-order syntax, consisting of a first-order type signature,
     second-order term signature and second-order equational theory.
  """

  def __init__(self, syn_name, ty_sig, tm_sig, theory):
    self.syn_name = syn_name
    self.ty_sig = ty_sig
    self.tm_sig = tm_sig
    self.theory = theory
    self.tm_sig.extract_type_vars(ty_sig.symbols)

    self.tm_sig.all_ty_vars()
    self.tm_sig.ty_name = ty_sig.name

  def render_agda(self, out):
    """Render the Agda files for the signature.
    """
    if not out:
      out = Path("out")
    temp_strings = {
      'syn_name': self.syn_name,
      'type': self.ty_sig.name,
      'type_fixity':          '\n' + '\n'.join(self.ty_sig.render_fixity()) + '\n',
      'type_decl':            self.ty_sig.render_all(),
      'derived_ty_ops':       "\n".join(["\n-- Derived types"] + [f"{op.name} : {(self.ty_sig.name + ' → ')*op.arity + self.ty_sig.name}\n{op.name} = ?" for op in self.ty_sig.derived_ty_ops]) if self.ty_sig.derived_ty_ops else "",
      'ty_vars':              ' '.join(self.tm_sig.ty_vars),
      'fst_ty_var':           self.tm_sig.ty_vars[0],
      'operator_decl':        '\n  '.join(self.tm_sig.render_op_symbols()),
      'sig_string' :          str(self),
      'sig':                  self.tm_sig.name,
      'sig_decl':             '\n  ; '.join(self.tm_sig.render_tm_sig()),
      'syn_constructors':     '\n    '.join([op.render_op_ctor(self.tm_sig.name) for op in self.tm_sig.ops]),
      'op_fixity':            '\n  '.join(self.tm_sig.render_op_fixity()),
      'alg_patterns':         "\n      ".join([op.render_alg_pat() for op in self.tm_sig.ops]) if self.tm_sig.ops else "()",
      'sem_patterns':         "\n    ".join([op.render_sem_pat() for op in self.tm_sig.ops]),
      'alg_hom_patterns':     "\n      ".join([op.render_alg_hom_pat() for op in self.tm_sig.ops]) if self.tm_sig.ops else "⟨𝑎𝑙𝑔⟩ ()",
      'alg_unique_patterns':  "\n      ".join([op.render_alg_unique_pat() for op in self.tm_sig.ops]),
      'derived_tm_ops':       "\n".join(["-- Derived operations"] + [f"{op.render_op_ctor(self.tm_sig.name + ' 𝔛')}\n{op.sym} = ?" for op in self.tm_sig.derived_tm_ops]) if self.tm_sig.derived_tm_ops else "",
      'axioms':               "\n  ".join(self.theory.render_axioms()) if self.theory.eqs else "",
      'derived_eqs':          "\n".join(['-- Derived equations'] + [f"{eq.render(eq_sign='≋')}\n{eq.derived_def or eq.name + ' = ?'}" for eq in self.theory.derived_eqs] if self.theory.derived_eqs else "")
    }
    result = ""

    if not path.exists(path.join(out, self.syn_name)):
      os.makedirs(path.join(out, self.syn_name))
    for tf in os.listdir(path.join('gen','templates')):
      if not self.theory and tf == "Equality.agda":
        continue
      with open(path.join('gen','templates',tf), 'r') as f:
        src = Template(f.read())
        result = src.substitute(temp_strings)
      with open(path.join(out, self.syn_name, tf), "w") as output:
        output.write(result)

  def derive_tokens(self, tokens):
    """Mark operations or equations as derived.
    """
    for op in self.ty_sig.all_ops:
      if op.name in tokens: op.derived = True
    for op in self.tm_sig.all_ops:
      if op.name in tokens or op.sym in tokens: op.derived = True

    for eq in self.theory.all_eqs:
      if eq.name in tokens: eq.derived = True


  def hide_tokens(self, tokens):
    """Delete tokens (types, terms, equations) from the syntax.
    """
    self.ty_sig.all_ops = [op for op in self.ty_sig.all_ops if op.name not in tokens and op.name != "*"]
    self.tm_sig.all_ops = [op for op in self.tm_sig.all_ops if op.name not in tokens and op.sym not in tokens]
    self.theory.all_eqs = [eq for eq in self.theory.all_eqs if eq.name not in tokens]

  def keep_tokens(self, tokens):
    """Keep specified tokens (types, terms, equations) from the syntax.
    """
    self.ty_sig.all_ops = [op for op in self.ty_sig.all_ops if op.name in tokens or op.name == "*"]
    self.tm_sig.all_ops = [op for op in self.tm_sig.all_ops if op.name in tokens or op.sym in tokens]
    self.theory.all_eqs = [eq for eq in self.theory.all_eqs if eq.name in tokens]

  def rename_tokens(self, ren_dict):
    """Change full token names.

    Args:
        ren_dict (dict[str, str]): Mapping from old names to new.
    """
    for tm_op in self.tm_sig.all_ops:
      if tm_op.name in ren_dict: tm_op.name = ren_dict[tm_op.name]
      if tm_op.sym in ren_dict: tm_op.sym = ren_dict[tm_op.sym]

    for eq in self.theory.all_eqs:
      if eq.name in ren_dict: eq.name = ren_dict[eq.name]
      eq.raw_str = apply_replacements(eq.raw_str, ren_dict)
      eq.tm1.apply_ren(ren_dict)
      eq.tm2.apply_ren(ren_dict)
    for prop in self.theory.props:
      for k, v in prop.__dict__.items():
        if v in ren_dict: prop.__dict__[k] = ren_dict[v]
    new_ops = {}
    for o, s in self.theory.ops.items():
      new_ops[ren_dict[o] if o in ren_dict else o] = ren_dict[s] if s in ren_dict else s
    self.theory.ops = new_ops

  def rename_sym_in_tokens(self, ren_dict):
    """Change occurrences of symbols in tokens.

    Args:
        ren_dict (dict[str, str]): Mapping from old symbols to new.
    """
    for tm_op in self.tm_sig.all_ops:
      tm_op.name = apply_replacements(tm_op.name, ren_dict)
      tm_op.sym = apply_replacements(tm_op.sym, ren_dict)
    for eq in self.theory.all_eqs:
      eq.name = apply_replacements(eq.name, ren_dict)
      eq.raw_str = apply_replacements(eq.raw_str, ren_dict)
      eq.tm1.apply_ren_sym(ren_dict)
      eq.tm2.apply_ren_sym(ren_dict)
    for prop in self.theory.props:
      for k, v in prop.__dict__.items():
        if v in ren_dict: prop.__dict__[k] = apply_replacements(prop.__dict__[k], ren_dict)
    new_ops = {}
    for o, s in self.theory.ops.items():
      new_k = apply_replacements(o, ren_dict)
      new_v = apply_replacements(s, ren_dict)
      new_ops[new_k] = new_v
    self.theory.ops = new_ops

  def change_fixity(self, fix_dict):
    for tm_op in self.tm_sig.all_ops:
      if tm_op.name in fix_dict:
        tm_op.infix_spec = fix_dict[tm_op.name]


  def spec(self):
    return {'TypeSignature' : self.ty_sig.spec(), 'TermSignature': self.tm_sig.spec()}

  def __repr__(self):
    return str(self.spec())

  def __str__(self):
    return (f"syntax {self.syn_name + (' | ' + self.tm_sig.name if self.tm_sig.name != self.syn_name else '')}\n\n{str(self.ty_sig)}\n\n{str(self.tm_sig)}\n\ntheory\n  " + "\n  ".join([str(eq) for eq in self.theory.all_eqs]))

def combine_syntaxes(syn1: Syntax, syn2: Syntax, syn_name="", tm_name=""):
  """Combine two syntaxes into one.

  Args:
      syn1 (Syntax): Base syntax
      syn2 (Syntax): Extension syntax
      syn_name (str, optional): Override syntax name. Defaults to "".
      tm_name (str, optional): Override term signature name. Defaults to "".

  Returns:
      Syntax: Combined syntax
  """
  override = syn2.tm_sig.name != syn2.syn_name
  if isinstance(syn2.ty_sig, Unsorted): # Handle unsorted type signatures separately
    if not syn1.ty_sig.ops or not syn2.ty_sig.ops:
      com_ty_sig = Unsorted()
    else:
      com_ty_sig = syn1.ty_sig
  else:
    com_ty_sig = TypeSignature(syn2.ty_sig.name if override else syn1.ty_sig.name, *OrderedDict.fromkeys(syn1.ty_sig.all_ops + syn2.ty_sig.all_ops))
  com_tm_sig = TermSignature(syn2.tm_sig.name if override else syn1.tm_sig.name, *OrderedDict.fromkeys((syn1.tm_sig.all_ops + syn2.tm_sig.all_ops)))
  if tm_name:
    if not isinstance(com_ty_sig, Unsorted):
      com_ty_sig.name = tm_name + "T"
    com_tm_sig.name = tm_name

  com_thr = Theory(list_union(syn1.theory.props, syn2.theory.props), list_union(syn1.theory.new_eqs, syn2.theory.new_eqs), com_tm_sig.op_sym_dict)
  return Syntax(
    syn_name or syn2.syn_name,
    com_ty_sig, com_tm_sig,
    com_thr)
  
def combine_syntax_list(syns: list[Syntax]):
  """Combine a list of syntax descriptions"""
  if len(syns) == 1:
    return syns[0]
  return combine_syntaxes(combine_syntax_list(syns[:-1]), syns[-1])


def op(op_desc, sym=None, infix=None, derived=False):
  """Parse operator description."""
  name, *ty = op_desc.split(":")
  *arg_tys, ret_ty = splitstrip(ty[0], "->")
  return Op(
    name.strip(), 
    *split_spaces(arg_tys[0]) if arg_tys else [], 
    sort=ret_ty.strip(), 
    sym=sym, 
    infix=infix, 
    derived=derived)

def parse_mods(mods):
  """Parse import modifiers: hiding, using, renaming."""
  mods = splitstrip(mods, ";")
  mod_dict = {m.split()[0] : splitstrip(m[len(m.split()[0]):], ",") for m in mods}
  if 'renaming' in mod_dict:
    mod_dict['renaming_sym'] = dict([(splitstrip(s[6:], "to")) for s in mod_dict['renaming'] if "symbol" in s])
    ren_dict = dict([(splitstrip(s, "to")) for s in mod_dict['renaming'] if "symbol" not in s])
    mod_dict['renaming'] = ren_dict.copy()
    for k, v in ren_dict.items():
      # Handle parallel name:symbol renames
      if ":" in k and ":" in v:
        kw, ks = splitstrip(k, ":")
        vw, *vs = splitstrip(v, ":")
        mod_dict['renaming'][kw] = vw
        mod_dict['renaming_sym'][ks] = vs[0]
        # Fixity redeclaration
        if len(vs) == 2:
          if 'fixity' in mod_dict:
            mod_dict['fixity'][kw] = vs[1]
          else:
            mod_dict['fixity'] = {kw : vs[1]}
      else:
        mod_dict['renaming'][k] = v
    if 'using' in mod_dict:
      mod_dict['using'] = mod_dict['using'] + list(mod_dict['renaming'].keys())
    if 'hiding' in mod_dict:
      mod_dict['hiding'] = [t for t in mod_dict['hiding'] if t not in mod_dict['renaming'].keys()]
  return mod_dict


def read_syn(file):
  """Read syntax file.

  Args:
      file (str): File path containing syntax description.

  Raises:
      Exception: [description]

  Returns:
      Syntax: Syntax extracted from the file.
  """
  ls = []
  path = Path(file)
  dirname = path.parent
  with open(file, 'r') as fp:
    ls = [l.rstrip() for l in fp.read().splitlines() if l and not l.strip().startswith('--')]
  has_ty, has_tm, has_th = [kw in ls for kw in ["type", "term", "theory"]]

  # Collect type signature lines
  ty_lines =  []
  if has_ty:
    ty_pos = ls.index("type")
    for l in ls[ty_pos+1:]:
      if not re.search("^\s+.*$", l):
        break
      ty_lines.append(l.strip())

  # Collect term signature lines
  tm_lines = []
  if has_tm:
    tm_pos = ls.index("term")

    for l in ls[tm_pos+1:]:
      if not re.search("^\s+.*$", l):
        break
      tm_lines.append(l.strip())

  # Collect equation and property lines
  eq_lines = []
  prop_lines = []
  if has_th:
    th_pos = ls.index("theory")
    for l in ls[th_pos+1:]:
      if not re.search("^\s+.*$", l):
        break
      # Handle line breaks
      if not (l.strip().startswith("{") or l.strip().startswith("(") or l.strip().startswith("'")):
        prev_l = eq_lines.pop()
        eq_lines.append(prev_l + " " + l.strip())
      elif l.strip().startswith("'"):
        prop_lines.append(l.strip())
      else:
        eq_lines.append(l.strip())

  # Parsing type operators
  ty_ops = []
  derived = False
  for l in ty_lines:
    if l[0] == "{" and l[-1] == "}":
      derived = True
      l = l[1:-1]      

    nm, sig = splitstrip(l, ':')
    if '|' in sig:
      ar, fix = splitstrip(sig, '|')
    else:
      ar, fix = sig[0], None
    ty_ops.append(TyOp(nm, int(ar[0]), fix, derived))

  # Parsing term operators
  tm_ops = []
  derived = False
  for l in tm_lines:
    if l[0] == "{" and l[-1] == "}":
      derived = True
      l = l[1:-1]      
    if '|' in l:
      sig, props = splitstrip(l, '|')
      sym, *fix = props.split()
    else:
      sig = l
      sym, fix = None, None
    tm_ops.append(op(sig, sym, fix[0] if fix else None, derived))

  # Extract signature name
  if "|" in ls[0]:
    m = re.search("^syntax ([^ ]*) *\| *([^ ]*)", ls[0])
    syn_name = m.group(1)
    tm_name = m.group(2)
  else:
    m = re.search("^syntax ([^ ]*)", ls[0])
    syn_name = m.group(1)
    tm_name = m.group(1)
  ty_name = tm_name + "T"

  if "extends" in ls[0]:  # Syntax extends another file
    if ls[0].strip().endswith('extends'): # Extension with modification
      ext_list = []
      i = 1
      while i < len(ls):
        l = ls[i].strip()
        if l.startswith("- "):
          ext_list.append(ls[i])
        elif l != "type" and l != "term" and l != "theory":
          # Handle line breaks
          prev_l = ext_list.pop()
          ext_list.append(prev_l + l)
        else: break
        i += 1

      mod_syns = []
      for ext in ext_list:
        m = re.search('\s*-\s+([^ ]+)(?:\s*\(([^)]*)\))?', ext)
        f, mods = m.groups()
        # Recursively read base syntax files
        syn = read_syn(PurePath(dirname,f)) 
        # Apply modifiers
        if mods:
          if "using" in mods and "hiding" in mods:
            raise Exception("The 'hiding' and 'using' modifiers are not allowed together.")
          mod_dict = parse_mods(mods)
          if 'hiding' in mod_dict:
            syn.hide_tokens(mod_dict['hiding'])
          elif 'using' in mod_dict:
            syn.keep_tokens(mod_dict['using'])
          if 'deriving' in mod_dict:
            syn.derive_tokens(mod_dict['deriving'])
          if 'fixity' in mod_dict:
            syn.change_fixity(mod_dict['fixity'])
          if 'renaming' in mod_dict:
            syn.rename_tokens(mod_dict['renaming'])
          if 'renaming_sym' in mod_dict:
            syn.rename_sym_in_tokens(mod_dict['renaming_sym'])
         
        mod_syns.append(syn)

      base_syn = combine_syntax_list(mod_syns)

    else: # Extension without modification
      m = re.search("extends (.*)$", ls[0])
      files = splitstrip(m.group(1), ",")
   
      base_syns = [read_syn(PurePath(dirname,f)) for f in files]
      base_syn = combine_syntax_list(base_syns)

    ops = {op.name : op.sym for op in base_syn.tm_sig.all_ops + tm_ops}

    ext_syn = Syntax(syn_name, 
      TypeSignature(ty_name, *ty_ops) if has_ty else Unsorted(),
      TermSignature(tm_name, *tm_ops),
      Theory.mk(prop_lines, eq_lines, ops))
    return combine_syntaxes(base_syn, ext_syn, syn_name, tm_name)

  else: # No extension
    ops = {op.name : op.sym for op in tm_ops}
    return Syntax(syn_name, 
      TypeSignature(ty_name, *ty_ops) if has_ty else Unsorted(),
      TermSignature(tm_name, *tm_ops),
      Theory.mk(prop_lines, eq_lines, ops))
    
if __name__ == "__main__":
  arg_parser = argparse.ArgumentParser(prog="soas", description='Produce an Agda formalisation from a syntax description file')
  arg_parser.add_argument("Syntax", metavar="path",type=Path, help="path to syntax file")
  arg_parser.add_argument("-o", "--out", type=Path, action="store", help="output folder for generated Agda modules")

  args = arg_parser.parse_args()
  syntax = read_syn(args.Syntax)
  syntax.render_agda(args.out)
  print(syntax.syn_name + " syntax generated successfully.")
