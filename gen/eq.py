"""Equational theory of a syntax"""

from .util import *
from .term import *
import re
from enum import Enum

class Term:
  """Top-level term in a object- and metavariable context
  """ 
  def __init__(self, ctx, mctx):
    self.ctx = ctx
    self.mctx = mctx
  
  def render(self):
    """Render a term as a string.
    """
    raise Exception("Abstract method")

  def apply_ren(self, ren_dict):
    """Apply a renaming to a term."""
    raise Exception("Abstract method")

  def apply_ren_sym(self, ren_dict):
    """Apply a symbol renaming to a term."""
    raise Exception("Abstract method")

  def parse_term(s, ctx, mctx, ops):
    """Parse a term consisting of operators, variables and metavariables.

    Args:
        s (str): Input string
        ctx (list[str]): Object variable context
        mctx (list[str]): Metavariable context
        ops (dict[str, str]): Mapping of operator names to symbols

    Returns:
        Term: Parsed term
    """
    s = strip_parens(s.strip())
    if re.search("^\w*$",s): # If a single word, either a variable or a constant
        if s in ops:
            return Con(ops[s], [], ctx, mctx)
        elif s in ctx:
            return Var(s, ctx, mctx)
        elif s in mctx:
            return MVar(s, [], ctx, mctx)
        elif s.startswith("O") and s[1:] in mctx:
            return MVar(s, [], ctx, mctx, is_hole=True)
        else:
            raise Exception("Unbound variable: " + "'" + s + "'")

    elif re.search("^\w*\[.*\]$", s): # If a metavariable
        m = re.search("^(\w)*\[(.*)\]$", s)
        mvar = m.group(1)
        env = m.group(2)
        if not env:
            return MVar(mvar, [], ctx, mctx, is_hole=mvar.startswith("O"))
        else:
            return MVar(mvar, [Term.parse_term(t, ctx, mctx, ops) for t in split_tuple(env)], ctx, mctx)

    elif re.search("^([\w ]*)\.(.*)$", s): # If a variable under binders
        m = re.search("^([\w ]*)\.(.*)$", s)
        bound = m.group(1).split()
        tm = m.group(2)
        return Term.parse_term(tm, bound + ctx, mctx, ops)

    elif re.search("^(\w*) *\((.*)\)$", s): # If an expression
        m = re.search("^(\w*) *\((.*)\)$", s)
        op = m.group(1)
        args = m.group(2)
        return Con(ops[op], [Term.parse_term(t, ctx, mctx, ops) for t in split_tuple(args)], ctx, mctx)
    else:
        raise Exception("Can't parse: " + s)
      
  def __repr__(self):
    return str(vars(self))
    
class Var(Term):
  """Variables are terms with a de Bruijn index.
  """
  def __init__(self, var, ctx, mctx):
    super().__init__(ctx, mctx)
    self.db = ctx.index(var)

  def apply_ren(self, ren_dict):
      pass
  
  def apply_ren_sym(self, ren_dict):
      pass

  def render(self):
    return "x" + num_to_ix(self.db)

class MVar(Term):
  """Metavariables are terms with a metavariable de Bruijn index and a term environment.
  """
  def __init__(self, mvar, env, ctx, mctx, is_hole=False):
    super().__init__(ctx, mctx)
    self.mvar = mvar
    self.mdb = mctx.index(mvar.replace("O", ""))
    self.env = env
    self.is_hole = is_hole # If the metavariable intends to denote a hole in a congruence context.

  def apply_ren(self, ren_dict): 
      for t in self.env:
        t.apply_ren(ren_dict)

  def apply_ren_sym(self, ren_dict):
    for t in self.env:
      t.apply_ren_sym(ren_dict)

  def render(self):
    mvs = "◌" + num_to_uix(self.mdb) if self.is_hole else num_to_frak(self.mdb)
    return mvs + \
      (f"⟨ {' ◂ '.join([wrap(t.render(), sep='⟨ ')  for t in self.env])} ⟩" 
      if self.env else "")


class Con(Term):
  """A constructor is a term with a name and list of argument terms.
  """
  def __init__(self, name, args, ctx, mctx):
    super().__init__(ctx, mctx)
    self.name = name
    self.args = args

  def apply_ren(self, ren_dict):
      if self.name in ren_dict: self.name = ren_dict[self.name]
      for ar in self.args:
        ar.apply_ren(ren_dict)

  def apply_ren_sym(self, ren_dict):
    self.name = apply_replacements(self.name, ren_dict)
    for ar in self.args:
      ar.apply_ren_sym(ren_dict)

  def render(self):
    if self.args:
      if "_" in self.name:
        return fill_underscores(self.name, [t.render() if isinstance(t, MVar) else wrap(t.render()) for t in self.args])
      else:
        return self.name + " " + " ".join([wrap(t.render()) for t in self.args])
    else: return self.name


class Eq:
  """Equation between two second-order terms.
  """
  def __init__(self, name, mctx_s, ctx_s, tm1, tm2, ops, derived=False, raw_str=""):
    self.name = name
    mctx, self.mctx_tys = Eq.unzip_ctx(mctx_s)
    self.mctx_tys = [Op.parse_so_type(t) for t in self.mctx_tys]
    ctx, self.ctx_tys = Eq.unzip_ctx(ctx_s)
    self.tm1 = Term.parse_term(tm1, ctx, mctx, ops)
    self.tm2 = Term.parse_term(tm2, ctx, mctx, ops)
    self.derived = derived
    self.derived_def = ""
    self.raw_str = raw_str

  def __eq__(self, o: object) -> bool:
      return self.name == o.name

  def __hash__(self) -> int:
      return hash(self.name)

  def unzip_ctx(s):
    """Turn a [var : type] context into a list of variable names and types.

    Args:
        s (str): A string of double space-separated var : type pair list.

    Returns:
        (list[str], list[str]): The list of variable names and their types.
    """
    ctx = split_spaces(s)
    vs = []
    ts = []
    for v, *t in [(splitstrip(v, ":")) for v in ctx]:
      t = t[0] if t else "*"
      if " " in v:
        ws = v.split()
        vs += ws
        ts += [t] * len(ws)
      else:
        vs.append(v)
        ts.append(t)
    return (vs, ts)

  def render_ctx(ctx, sep="∙"):
    if not ctx:
      return "∅"
    else:
      return "⌊ " + f" {sep} ".join([wrap(t) for t in ctx]) + " ⌋"

  def render_comps(self):
    """Render components of an equality judgment: equality name, 
       metavariable context, object variable context, and the two terms.
    """
    mctx_str = ""
    if not self.mctx_tys:
      mctx_str = "⁅⁆"
    else:
      mctx_str = " ⁆ ⁅ ".join([f"{Eq.render_ctx(bound, '·')[2:-2]} ⊩ {ty}" if bound else ty for bound, ty in self.mctx_tys])
      mctx_str = "⁅ " + mctx_str + " ⁆̣"
    return(self.name, mctx_str, Eq.render_ctx(self.ctx_tys), self.tm1.render(), self.tm2.render())

  def render_padded(comps, pn, pm, pc, pt, eq_sign="≋ₐ"):
    """Render components with padding.

    Args:
        comps (list[(str, list[str], list[str], Term, Term)]): A list of equality components
        pn (int): Name padding
        pm (int): Metavariable context padding
        pc (int): Object variable context padding
        pt (int): Term padding
        eq_sign (str, optional): Equality sign to use between terms. Defaults to "≋ₐ".

    Returns:
        str: String representation of the equation.
    """
    n, m, c, t1, t2 = comps
    return f"{rpad(n, pn)} : {rpad(m, pm if '⁅⁆' not in m else pm-1)} ▹ {cpad(c, pc)} ⊢ {lpad(t1, pt)} {eq_sign} {t2}"


  def render(self, eq_sign="≋ₐ"):
    """Render equality without padding.

    Args:
        eq_sign (str, optional): Equality sign to use between terms. Defaults to "≋ₐ".

    Returns:
        str: String representation of the equality.
    """
    n, m, c, t1, t2 = self.render_comps()
    return Eq.render_padded((n, m, c, t1, t2), len(n), len(m), len(c), len(t1), eq_sign)
          
  def parse_equations(eqs, ops):
    """Parse list of equation strings.

    Args:
        eqs (list[string]): List of equation strings.
        ops (dict[str, str]): Mapping of operator names to symbols.

    Returns:
        (list[str], list[AlgProp]): The list of custom equations, and the list of algebraic properties.
    """
    eeqs = []
    prop_list = ['unit of', 'commutative', 'associative', 'distributes over', 'inverse of', 
                  'annihilates', 'idempotent', 'absorbs', 'absorptive', 'involutive']
    props = []
    for eq in eqs:
      if not any_in(prop_list, eq):
        eeqs.append(Eq.parse_eq(eq, ops))
      else:
        if 'unit of' in eq:
          m = re.search("^'(\w+)'\s+(left|right)?\s*unit of\s+'(\w+)'$", eq)
          unit, side, op = m.groups()
          props.append(Unit(unit, op, side))
        elif "annihilates" in eq: 
          m = re.search("^'(\w+)'\s+(left|right)?\s*annihilates\s+'(\w+)'$", eq)
          unit, side, op = m.groups()
          props.append(Annih(unit, op, side))
        elif "distributes over" in eq:
          m = re.search("^'(\w+)'\s+(left|right)?\s*distributes over\s+'(\w+)'$", eq)
          op1, side, op2 = m.groups()
          props.append(Dist(op1, op2, side))
        elif "absorbs" in eq:
          m = re.search("^'(\w+)'\s+(left|right)?\s*absorbs\s+'(\w+)'$", eq)
          op1, side, op2 = m.groups()
          props.append(Absorb(op1, op2, side))
        elif "inverse of" in eq:
          m = re.search("^'(\w+)'\s+(left|right)?\s*inverse of\s+'(\w+)'\s+with\s+'(\w+)'$", eq)
          uop, side, op, unit = m.groups()
          props.append(Inverse(uop, op, unit, side))
        elif "absorptive" in eq:
          m = re.search("^'(\w+)'\s+and\s+'(\w+)'\s+absorptive$", eq)
          op1, op2 = m.groups()
          props.append(Absorb(op1, op2, None))
          props.append(Absorb(op2, op1, None))
        else:
          m = re.search("^'(\w+)'\s+(.*)$", eq)
          op = m.group(1)
          kws = splitstrip(m.group(2), ",")
          if 'associative' in kws:
            props.append(Assoc(op))
          if 'commutative' in kws:
            props.append(Comm(op))
          if 'idempotent' in kws:
            props.append(Idemp(op))
          if 'involutive' in kws:
            props.append(Invol(op))

    return eeqs, props

  def prop_to_eq(prop, all_props, ops):
    """Convert property to equation, marking it as 'derivable' if it 
       is directed and the top-level operator is commutative.

    Args:
        prop (AlgProp): Algebraic property
        all_props (list[AlgProp]): List of existing algebraic properties
        ops (dict[str, str]): Mapping of operator names to symbols.

    Returns:
        Eq: Equation based on the property, optionally derivable.
    """
    if isinstance(prop, DirAlgProp) and Comm(prop.op) in all_props:
      prop.side = Side.BOTH
      prop.derived = True
      return prop.eq(ops)
    else:
      return prop.eq(ops)

  def parse_prop(s):
    """Parse algebraic property.

    Args:
        s (str): String representation of algebraic property

    Returns:
        AlgProp: Appropriate algebraic property.
    """
    props = []

    if 'unit of' in s:
      m = re.search("^'(\w+)'\s+(left|right)?\s*unit of\s+'(\w+)'$", s)
      unit, side, op = m.groups()
      props.append(Unit(unit, op, side))
    elif "annihilates" in s: 
      m = re.search("^'(\w+)'\s+(left|right)?\s*annihilates\s+'(\w+)'$", s)
      unit, side, op = m.groups()
      props.append(Annih(unit, op, side))
    elif "distributes over" in s:
      m = re.search("^'(\w+)'\s+(left|right)?\s*distributes over\s+'(\w+)'$", s)
      op1, side, op2 = m.groups()
      props.append(Dist(op1, op2, side))
    elif "absorbs" in s:
      m = re.search("^'(\w+)'\s+(left|right)?\s*absorbs\s+'(\w+)'$", s)
      op1, side, op2 = m.groups()
      props.append(Absorb(op1, op2, side))
    elif "inverse of" in s:
      m = re.search("^'(\w+)'\s+(left|right)?\s*inverse of\s+'(\w+)'\s+with\s+'(\w+)'$", s)
      uop, side, op, unit = m.groups()
      props.append(Inverse(uop, op, unit, side))
    elif "absorptive" in s:
      m = re.search("^'(\w+)'\s+and\s+'(\w+)'\s+absorptive$", s)
      op1, op2 = m.groups()
      props.append(Absorb(op1, op2, None))
      props.append(Absorb(op2, op1, None))
    else:
      m = re.search("^'(\w+)'\s+(.*)$", s)
      op = m.group(1)
      kws = splitstrip(m.group(2), ",")
      if 'associative' in kws:
        props.append(Assoc(op))
      if 'commutative' in kws:
        props.append(Comm(op))
      if 'idempotent' in kws:
        props.append(Idemp(op))
      if 'involutive' in kws:
        props.append(Invol(op))

    return props


  def parse_eq(s, ops):
    """Parse equation.

    Args:
        s (str): String representation of an equation
        ops (dict[str, str]): Mapping of operator names to symbols

    Returns:
        Eq: Parsed equation
    """
    derived = False
    if s[0] == "{" and s[-1] == "}": # If surrounded by {...}, equation is derived
      derived = True
      s = s[1:-1]
    if "|-" in s: 
      m = re.search("^\(([^ )]+)\)([^|]*)\|>([^|]*)\|-([^=]*)=([^=]*)$", s)
      if not m: raise Exception("Syntax error: " + s)
      name, mctx_s, ctx_s, tm1, tm2 = [m.group(n).strip() for n in range(1,6)]
    else: # Object variable context is optional
      m = re.search("^\(([^ )]+)\)([^|]*)\|>([^=]*)=([^=]*)$", s)
      if not m: raise Exception("Syntax error: " + s)
      name, mctx_s, tm1, tm2 = [m.group(n).strip() for n in range(1,5)]
      ctx_s = ""

    return Eq(name, mctx_s, ctx_s, tm1, tm2, ops, derived, s)

  def __str__(self):
    return self.raw_str
  def __repr__(self):
    return str(vars(self))

class Theory:
  """Equational theory of a second-order syntax, consisting of equations and algebraic properties.
  """
  def __init__(self, props, new_eqs, ops):
      self.props = props
      self.new_eqs = new_eqs
      self.ops = ops

  @property
  def all_eqs(self):
    return list(dict.fromkeys(flatten([Eq.prop_to_eq(p, self.props,self.ops) for p in self.props]) + self.new_eqs))

  @property
  def eqs(self):
    return [eq for eq in self.all_eqs if not eq.derived]

  @property
  def derived_eqs(self):
    return [eq for eq in self.all_eqs if eq.derived]

  @staticmethod
  def mk(prop_lines, eq_lines, ops):
    """Construct theory from string descriptions of properties and equations.

    Args:
        prop_lines (list[str]): Algebraic properties as strings
        eq_lines (list[str]): Equations as strings
        ops (dict[str, str]): Mapping of operator names to symbols

    Returns:
        Theory: Theory with properties and equations.
    """
    props = flatten([Eq.parse_prop(pl) for pl in prop_lines])
    eqs = [Eq.parse_eq(el, ops) for el in eq_lines]
    return Theory(props, eqs, ops)

  def render_axioms(self):
    """Render equational axioms with padding

    Returns:
        list[str]: Rendered equations
    """
    mn, mm, mc, mt = 0, 0, 0, 0
    comps = [eq.render_comps() for eq in self.eqs]
    for n, m, c, t1, _ in comps:
      if mn < len(n): mn = len(n)
      if mm < len(m): mm = len(m)
      if mc < len(c): mc = len(c)
      if mt < len(t1): mt = len(t1)
    return [Eq.render_padded(cs, mn, mm, mc, mt) for cs in comps]

class AlgProp:
  """Base class for equational properties.
  """
  def __eq__(self, o: object) -> bool:
    if isinstance(o, self.__class__):
      return self.__dict__ == o.__dict__
    else:
      return NotImplemented

  def __repr__(self) -> str:
    return str((self.__class__.__name__)) + " " + str(vars(self))

  def __hash__(self) -> int:
      return hash(tuple(sorted(self.__dict__.items())))

class Comm(AlgProp):
  """Commutativity"""
  def __init__(self, op) -> None:
      self.op = op

  def eq(self, ops):
    return [Eq.parse_eq(f"({ops[self.op].strip('_')}C) a b |> {self.op}(a, b) = {self.op}(b, a)", ops)]

class Assoc(AlgProp):
  """Associativity"""
  def __init__(self, op) -> None:
      self.op = op
        
  def eq(self, ops):
    return [Eq.parse_eq(f"({ops[self.op].strip('_')}A) a b c |> {self.op} ({self.op}(a, b), c) = {self.op} (a, {self.op}(b, c))", ops)]

class Idemp(AlgProp):
  """Idempotence"""
  def __init__(self, op) -> None:
    self.op = op

  def eq(self, ops):
    return [Eq.parse_eq(f"({ops[self.op].strip('_')}I) a |> {self.op}(a, a) = a", ops)]

class Invol(AlgProp):
  """Involution"""
  def __init__(self, op) -> None:
    self.op = op

  def eq(self, ops):
    return [Eq.parse_eq(f"({ops[self.op].strip('_')}²) a |> {self.op}({self.op} (a)) = a", ops)]


class Side(Enum):
  """Orientation of directed properties (e.g. left unit, right distributivity).
  """
  LEFT = 1
  RIGHT = 2
  BOTH = 3

class DirAlgProp(AlgProp):
  """Directed algebraic property with a top-level binary operation and an orientation.
  """
  def __init__(self, op, side) -> None:
    super().__init__()
    self.op = op
    self.side = Side.BOTH if not side else (Side.LEFT if 'left' in side else Side.RIGHT)
    self.derived = False

  def eqs_and_deriv(self, _):
    """Left and right equations, and derived definition.
    """
    pass

  def eq(self, ops):
    """A directed property may give rise to two equations, 
       with the right one potentially derivable from the left one."""
    left, right, deriv = self.eqs_and_deriv(ops)
    eqs = []
    if self.side in [Side.LEFT, Side.BOTH]:
      eqs.append(Eq.parse_eq(left, ops))
    # Add the right-side equation with its derivation 
    if self.side in [Side.RIGHT, Side.BOTH]:
      eq = Eq.parse_eq(right, ops)
      eq.derived_def = deriv
      eq.derived = self.derived
      eqs.append(eq)
    return eqs


class Unit(DirAlgProp):
  """Unit"""
  def __init__(self, unit, op, side) -> None:
    super().__init__(op, side)
    self.unit = unit

  def eqs_and_deriv(self, ops):
    op_sym = ops[self.op].strip('_')
    return (
      f"({ops[self.unit]}U{op_sym}ᴸ) a |> {self.op} ({self.unit}, a) = a",
      f"({ops[self.unit]}U{op_sym}ᴿ) a |> {self.op} (a, {self.unit}) = a",
      f"{ops[self.unit]}U{op_sym}ᴿ = tr (ax {op_sym}C with《 𝔞 ◃ {ops[self.unit]} 》) (ax {ops[self.unit]}U{op_sym}ᴸ with《 𝔞 》)")

class Annih(DirAlgProp):
  """Annihilation"""
  def __init__(self, unit, op, side) -> None:
    super().__init__(op, side)
    self.unit = unit

  def eqs_and_deriv(self, ops):
    op_sym = ops[self.op].strip('_')
    return (
      f"({ops[self.unit]}X{op_sym}ᴸ) a |> {self.op} ({self.unit}, a) = {self.unit}",
      f"({ops[self.unit]}X{op_sym}ᴿ) a |> {self.op} (a, {self.unit}) = {self.unit}",
      f"{ops[self.unit]}X{op_sym}ᴿ = tr (ax {op_sym}C with《 𝔞 ◃ {ops[self.unit]} 》) (ax {ops[self.unit]}X{op_sym}ᴸ with《 𝔞 》)")

class Absorb(DirAlgProp):
  """Absorption"""
  def __init__(self, op, op2, side) -> None:
    super().__init__(op, side)
    self.op2 = op2
    
  def eqs_and_deriv(self, ops):
    op1_sym = ops[self.op].strip('_')
    op2_sym = ops[self.op2].strip('_')
    return (
      f"({op1_sym}B{op2_sym}ᴸ) a b |> {self.op} ({self.op2} (a, b), a) = a",
      f"({op1_sym}B{op2_sym}ᴿ) a b |> {self.op} (a, {self.op2} (a, b)) = a",
      f"{op1_sym}B{op2_sym}ᴿ = tr (ax {op1_sym}C with《 𝔞 ◃ ({Term.parse_term(f'{self.op2} (a, b)', [], ['a','b'],ops).render()}) 》) (ax {op1_sym}B{op2_sym}ᴸ with《 𝔞 ◃ 𝔟 》)")

class Inverse(DirAlgProp):
  """Inverse"""
  def __init__(self, uop, bop, unit, side) -> None:
    super().__init__(bop, side)
    self.uop = uop
    self.unit = unit

  def eqs_and_deriv(self, ops):
    uop_sym = ops[self.uop].strip('_')
    bop_sym = ops[self.op].strip('_')
    return (
      f"({uop_sym}N{bop_sym}ᴸ) a |> {self.op} ({self.uop} (a), a) = {self.unit}",
      f"({uop_sym}N{bop_sym}ᴿ) a |> {self.op} (a, {self.uop} (a)) = {self.unit}",
      f"{uop_sym}N{bop_sym}ᴿ = tr (ax {bop_sym}C with《 𝔞 ◃ ({Term.parse_term(f'{self.uop} (a)', [], ['a'],ops).render()}) 》) (ax {uop_sym}N{bop_sym}ᴸ with《 𝔞 》)")


class Dist(DirAlgProp):
  """Distributivity"""
  def __init__(self, op, op2, side) -> None:
    super().__init__(op, side)
    self.op2 = op2

  def eqs_and_deriv(self, ops):
    op1_sym = ops[self.op].strip('_')
    op2_sym = ops[self.op2].strip('_')
    symb = lambda s: Term.parse_term(s, [], ['a','b','c','d','e'], ops).render()
    return (
      f"({op1_sym}D{op2_sym}ᴸ) a b c |> {self.op} (a, {self.op2} (b, c)) = {self.op2} ({self.op}(a, b), {self.op}(a, c))",
      f"({op1_sym}D{op2_sym}ᴿ) a b c |> {self.op} ({self.op2} (a, b), c) = {self.op2} ({self.op}(a, c), {self.op}(b, c))",
      (f"{op1_sym}D{op2_sym}ᴿ = begin\n  "
          f"{symb(f'{self.op} ({self.op2} (a, b), c)')}       ≋⟨ ax {op1_sym}C with《 {symb(f'{self.op2} (a, b)')} ◃ 𝔠 》 ⟩\n  "
          f"{symb(f'{self.op} (c, {self.op2} (a, b))')}       ≋⟨ ax {op1_sym}D{op2_sym}ᴸ with《 𝔠 ◃ 𝔞 ◃ 𝔟 》 ⟩\n  "
          f"{symb(f'{self.op2} ({self.op}(c, a),{self.op}(c,b))')}  ≋⟨ cong₂[ ax {op1_sym}C with《 𝔠 ◃ 𝔞 》 ][ ax {op1_sym}C with《 𝔠 ◃ 𝔟 》 ]inside {symb(f'{self.op2} (Od, Oe)')} ⟩\n  "
          f"{symb(f'{self.op2} ({self.op}(a, c),{self.op}(b,c))')}  ∎"))

