"""Term operators and signatures."""

from collections import defaultdict
from gen.type import Unsorted
from .util import *


class Op:
  """Operator of the term syntax.
  """
  def __init__(self, name, *args, sort, sym=None, infix=None, derived=False):
    """Construct an operator for the term syntax.

    Args:
        name (str): Name of the operator
        *args (list[str]): Operator arguments
        sort (str): Sort of the operator
        sym (str, optional): Symbol for the operator. Defaults to None.
        infix (str, optional): Fixity for the operator. Defaults to None.
    """
    self.name = name
    self.arity = len(args)
    self.arity_diff = 0 # Used to figure out the operator with the most number of arguments
    self.sort = sort
    self.args = [Op.parse_so_type(t) for t in args]
    # Op.parse_args(args)
    # Tokens that make up the sort and arguments, from which the type variables will be extracted
    # sort_tokens = strip_parens(sort).split(" ")
    # arg_tokens = [flatten([strip_parens(bty).split(" ") for bty in bound]) + strip_parens(ty).split(" ") for (bound, ty) in self.args]
    # self.all_tokens = set(flatten(arg_tokens)).union(sort_tokens)
    self.ty_vars = []
    self.derived = derived

    # Name and symbol padding used for alignment
    self.padding = 0
    self.sym_padding = 0
    self.sym = sym or name

    self.infix_spec = infix
    # self.infix = None
    # if infix:
    #     if infix[0] in ['l', 'r']:
    #       self.infix = (infix[0], infix[1:])
    #     else: self.infix = ('', infix)

  def __eq__(self, o: object) -> bool:
      return self.name == o.name

  def __hash__(self) -> int:
      return hash(self.name)

  @property
  def infix(self):
    if not self.infix_spec: return None
    if self.infix_spec[0] in ['l', 'r']:
      return (self.infix_spec[0], self.infix_spec[1:])
    else: return  ('', self.infix_spec)


  @property
  def all_tokens(self):
    sort_tokens = strip_parens(self.sort).split(" ")
    arg_tokens = [flatten([strip_parens(bty).split(" ") for bty in bound]) + strip_parens(ty).split(" ") for (bound, ty) in self.args]
    return set(flatten(arg_tokens)).union(sort_tokens)


  @staticmethod
  def parse_so_type(s):
    """Parse a type with bound arguments.

    Args:
        s (string): A type with optional bound arguments.

    Returns:
        string: A pair of a list of bound arguments and return sort
    """
    if '.' in s:
      ty_bound = splitstrip(s, '.')
      ty = strip_parens(ty_bound[1])
      bound = [t for t in splitstrip(strip_parens(ty_bound[0]), ',')]
    else:
      ty = s.strip()
      bound = []

    return (bound, ty)

  @staticmethod
  def parse_args(args):
    """Parse operator arguments

    Args:
        args (list[str]): The types of operator arguments

    Returns:
        (list[string], string): Pair of argument type and bound variables
    """
    bound_ty_pairs = []
    for arg in args:
        if '.' in arg:
          ty_bound = arg.split('.')
          ty = strip_parens(ty_bound[1]).strip()
          bound = [t.strip() for t in strip_parens(ty_bound[0].strip()).split(',')]
        else:
          ty = arg.strip()
          bound = []
        bound_ty_pairs.append((bound, ty))
    return bound_ty_pairs

  def remove_type_symbols(self, symbols):
    """Initialise the type variable list by removing the symbols from all tokens found in the operator.

    Args:
        symbols (list[string]): The symbols found in the type signature.
    """
    self.ty_vars = sorted(list(self.all_tokens.difference(symbols)))


  @staticmethod
  def render_argument(arg):
    """Render an argument with its bound variable list.

    Args:
        arg ((list[string], string)): A pair of argument sort and bound variable list.
    """
    bound, ty = arg
    bound_tys = ' , '.join(bound)
    return(wrap(appn(bound_tys, f"⊢{num_to_ix(len(bound))} {ty}")))

  def render_operator(self, padding=0):
    """Render signature for operator.

    Args:
        padding (int, optional): The padding used to align the constructors. Defaults to 0.
    """
    impl_params = '}{'.join(self.ty_vars)
    if self.ty_vars:
        pattern = f"({self.name}ₒ {' '*self.padding}{{{impl_params}}})"
    else:
        pattern = f" {self.name}ₒ {' '*self.padding}"

    args = [Op.render_argument(arg) for arg in self.args]
    arity = appn(' , '.join(args), f"⟼{num_to_ix(self.arity)} {self.sort}")
    return(f"{pattern}{' '*padding} → {arity}")

  def render_op_ty(self, aty, rty):
    """Render the type signature of an operator.

    Args:
        aty (string): Argument family
        rty (string): Return family

    Returns:
        string: Type signature of operator.
    """
    arg_tys = []
    for bound, ty in self.args + ([Op.parse_so_type(self.sort)] if self.derived else []):
      ctx = " ∙ ".join([wrap(t) for t in bound] + ["Γ"])
      arg_tys.append(f"{aty} {wrap(ty)} {wrap(ctx)}")
    if self.derived: # If derived, the output sort can include context extension as well
        return " → ".join(arg_tys)
    else:
      return " → ".join(arg_tys + [f"{rty} {wrap(self.sort)} Γ"])


  def render_op_ctor(self, fam):
    """Render data type constructor for the operator.

    Args:
        fam (string): Family of terms

    Returns:
        string: Type signature of the operator constructor.
    """
    return f"{self.sym}{' ' * self.sym_padding} : " + self.render_op_ty(fam, fam)


  def render_alg_pat(self):
    """Render pattern for the signature algebra instance.

    Returns:
        str: Pattern for the algebra declaration.
    """
    var_names = new_vars(self.arity)
    if self.arity:
      return f"({self.name}ₒ {' ' * self.padding}⅋ {' , '.join(var_names)}) {' ' * (4 * self.arity_diff)}→ {self.sym} " + (' ' * self.sym_padding) + ' '.join(var_names)
    else:

      return f"({self.name}ₒ {' ' * self.padding}⅋ _) {' ' * (4 * (self.arity_diff - 1))}→ {self.sym}"

  def render_sem_pat(self):
    """Render pattern for the semantic interpretation.

    Args:
        padding (int, optional): Padding used for alignment. Defaults to 0.
    """
    if self.arity:
      pattern = wrap(appn(self.sym + " " * self.sym_padding, " ".join(new_vars(self.arity))))
      args = ' , '.join(['𝕤𝕖𝕞 ' + arg for arg in new_vars(self.arity)])
    else:
      pattern = appn(" " + self.sym + " " * self.sym_padding + " ", " ".join(new_vars(self.arity)))
      args = 'tt'

    return f"𝕤𝕖𝕞 {pattern + ' ' * (self.arity_diff * 2)} = 𝑎𝑙𝑔 ({self.name}ₒ {' ' * self.padding}⅋ {args})"

  def render_alg_hom_pat(self):
    """Render pattern for algebra homomorphism instance.
    """
    return f"⟨𝑎𝑙𝑔⟩ ({self.name}ₒ {' ' * self.padding}⅋ _) = refl"

  def render_alg_unique_pat(self):
    """Render pattern for unique homomorphism proof.
    """
    var_names = new_vars(self.arity)
    l1 = f"𝕤𝕖𝕞! {wrap(appn(self.sym, ' '.join(var_names)))}"
    if self.arity:
        l1 += ' rewrite 𝕤𝕖𝕞! ' + ' | 𝕤𝕖𝕞! '.join(var_names)
    l2 = f" = sym ⟨𝑎𝑙𝑔⟩"

    return l1 + l2

  def sym_tyvar_len(self):
    """Length of signature declaration pattern, consisting of symbol and type arguments.
    """
    return len("".join(self.ty_vars)) + 2 * len(self.ty_vars) + (1 if self.ty_vars else 0)

  def spec(self):
    return {'OpName' : self.name, 'OpTyParams': self.ty_vars, 'OpSort' : self.sort , 'OpArity' : self.args}

  def __repr__(self):
    return str(self.spec())

  def __str__(self):
    arg_list = []
    for bound, ty in self.args:
      if bound:
        arg_list.append(f"{wrap(','.join(bound), ',')}.{wrap(ty)}")
      else:
        arg_list.append(ty)
    sym_suffix = f" | {self.sym} {self.infix_spec or ''}" if self.sym.title() != self.name.title() else ""
    if self.args:
        return f"{self.name + ' '*self.padding} : {'  '.join(arg_list)}  ->  {self.sort}" + sym_suffix
    else:
        return f"{self.name + ' '*self.padding} : {self.sort}" + sym_suffix


class TermSignature:
  """Term signature of a second-order syntax.
  """
  def __init__(self, name, *ops):
    self.name = name
    self.all_ops = list(ops)

    self.ty_vars = set()

    # Determine maximum operator arity, name and symbol length to calculate padding.
    max_op_length = max([len(op.name) for op in ops]) if ops else 0
    max_sym_length = max([len(op.sym) for op in ops]) if ops else 0
    max_arity = max([op.arity for op in ops]) if ops else 0
    for op in self.ops:
      op.padding = max_op_length - len(op.name)
      op.sym_padding = max_sym_length - len(op.sym)
      op.arity_diff = max_arity - op.arity
    self.ty_name = ""

  @property
  def ops(self):
    return [op for op in self.all_ops if not op.derived]

  @property
  def derived_tm_ops(self):
    return [op for op in self.all_ops if op.derived]

  @property
  def op_sym_dict(self):
    return {op.name : op.sym for op in self.ops}

  def extract_type_vars(self, ty_symbols):
    """Modify operators to only keep track of the free type variables in their signature.
    """
    for op in self.all_ops:
        op.remove_type_symbols(ty_symbols)

  def all_ty_vars(self):
    """Collect all type variables that occur in the operators.
    """
    ty_vars = set()
    for op in self.ops:
      ty_vars = ty_vars.union(set(op.ty_vars))
    self.ty_vars = sorted(ty_vars) if ty_vars else ['α']

  def render_op_symbols(self):
    """Render the operator symbols with their respective type variables.
    """
    op_sym_name = self.name + "ₒ"
    op_groups = defaultdict(list)
    for op in self.ops:
      params = " ".join(op.ty_vars)
      op_groups[params].append(op.name)
    ls = []
    for ty_params, ops in op_groups.items():
      names = " ".join([op + 'ₒ' for op in ops])
      if not ty_params:
        ls.append(f"{names} : {op_sym_name}")
      else:
        ls.append(f"{names} : {{{ty_params} : {self.ty_name}}} → {op_sym_name}")
    return ls


  def render_tm_sig(self):
    """Render term signature instance.
    """
    if isinstance(self, EmptySig):
      return ["()"]
    max_pattern_len = max([op.sym_tyvar_len() for op in self.ops]) if self.ops else 0
    ops = [op.render_operator(max_pattern_len - op.sym_tyvar_len()) for op in self.ops]

    return ops


  def render_op_fixity(self):
    """Render fixity information for operator.
    """
    ls = []
    for op in self.ops:
      if op.infix:
        assoc, infix = op.infix
        ls.append(f"infix{assoc} {infix} {op.sym}")
    return ls

  def render_syn_constructors(self):
    return [op.render_op_ctor(self.name) for op in self.ops]


  def spec(self):
    return {'SigName': self.name, 'Ops': [op.spec() for op in self.ops]}

  def __repr__(self):
    return str(self.spec())

  def __str__(self):
    ls = [f"term"]
    for op in self.ops:
        ls.append("  " + str(op))
    return '\n'.join(ls)

class EmptySig(TermSignature):
  def __init__(self):
    super().__init__("E")
