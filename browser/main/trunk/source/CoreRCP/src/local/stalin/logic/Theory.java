package local.stalin.logic;

import java.io.PrintWriter;
import java.io.Serializable;
import java.math.BigInteger;
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;

import local.stalin.util.UnifyHash;

/**
 * The theories defines the symbols and their axioms used in the logic.
 * There is one theory for a BoogiePL input.
 * @author hoenicke
 *
 */
public class Theory implements Serializable {

	private static final long serialVersionUID = 8970879070583963033L;

	public void setLogic(String logic) {
		this.logic = logic;
		if (logic.contains("UF")) 
			createSort("U", true);
		if (logic.contains("LRA") || logic.contains("LIRA")) {
			rationalSort = numericSort = createSort("Real", true);
			createNumericOperators(rationalSort, true);
		}
		if (logic.contains("LIA") || logic.contains("LIRA")) {
			numericSort = createSort("Int", true);
			createNumericOperators(numericSort, false);
		}
	}
	
	public String getLogic() {
		return logic;
	}
	
	public static final int hashConnectedFormula(int connector,Formula lhs,Formula rhs) {
		return (lhs.hashCode() ^ rhs.hashCode()) + connector * 1031;
	}
	private HashMap<String,List<FunctionSymbol>> functions =
		new HashMap<String,List<FunctionSymbol>>();
	private HashMap<String,List<PredicateSymbol>> predicates =
		new HashMap<String,List<PredicateSymbol>>();
	private HashMap<String,Sort> sorts = new HashMap<String,Sort>();
	
	private HashMap<String,List<FunctionSymbol>> tempfs =
		new HashMap<String, List<FunctionSymbol>>();
	private HashMap<String,List<PredicateSymbol>> tempps =
		new HashMap<String,List<PredicateSymbol>>();
	
	private List<Formula> axioms = new ArrayList<Formula>();
	
	private String logic;
	private Sort numericSort, rationalSort;
	
	private UnifyHash<NegatedFormula> notCache = new UnifyHash<NegatedFormula>();
	private UnifyHash<ConnectedFormula> conCache = new UnifyHash<ConnectedFormula>();
	private UnifyHash<ITEFormula> iteCache = new UnifyHash<ITEFormula>();
	private UnifyHash<QuantifiedFormula> qfCache = new UnifyHash<QuantifiedFormula>();
	private UnifyHash<FletFormula> fletCache = new UnifyHash<FletFormula>();
	private UnifyHash<LetFormula> letCache = new UnifyHash<LetFormula>();
	private UnifyHash<Atom> atomCache = new UnifyHash<Atom>();
	private UnifyHash<Term> termCache = new UnifyHash<Term>();
	private UnifyHash<TermVariable> tvunify = new UnifyHash<TermVariable>();
	private UnifyHash<FormulaVariable> fvunify = new UnifyHash<FormulaVariable>();
	
	private int tvarctr = 0;
	private int fvarctr = 0;
	/**
	 * Create a new theory.  Should be called once per input file.
	 * You should call setLogic afterwards.
	 */
	public Theory() {
	}
	public Formula internalAnd(Formula f, Formula g)
	{
		int hash = hashConnectedFormula(ConnectedFormula.AND,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.AND && (
					(conf.getLhs() == f && conf.getRhs() == g) || (conf.getLhs() == g && conf.getRhs() == f)) )
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.AND, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	
	public Formula and(Formula f, Formula g)
	{ 
		if (g == Atom.TRUE || f == Atom.FALSE) return f;
		if (g == Atom.FALSE || f == Atom.TRUE) return g;
		if( f == g ) return f;
		HashSet<Formula> seen = new HashSet<Formula>();
		Formula rhs = g;
		while (rhs instanceof ConnectedFormula &&
				((ConnectedFormula)rhs).getConnector() == ConnectedFormula.AND) {
			ConnectedFormula cf = (ConnectedFormula) rhs;
			seen.add(cf.getLhs());
			rhs = cf.getRhs();
		}
		seen.add(rhs);
		/* Normalize to right-assoc */
		Stack<Formula> fcomponents = new Stack<Formula>();
		while (f instanceof ConnectedFormula &&
				((ConnectedFormula)f).getConnector() == ConnectedFormula.AND) {
			fcomponents.push(((ConnectedFormula) f).getLhs());
			f = ((ConnectedFormula) f).getRhs();
		}
		Formula result = g;
		if (seen.add(f))
			result = internalAnd(f, result);
		while (fcomponents.size() > 0) {
			Formula subf = fcomponents.pop(); 
			if (seen.add(subf))
				result = internalAnd(subf, result);
		}
		return result;
	}
	
	@SuppressWarnings("unused")
	private Formula andz3(Formula lhs,Formula rhs) {
		int hash = hashConnectedFormula(ConnectedFormula.AND, lhs, rhs);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.AND && lhs == conf.getLhs() && rhs == conf.getRhs() )
				return conf;
		}
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.AND,lhs,rhs);
		conCache.put(hash,conf);
		return conf;
	}
	public Atom atom(FormulaVariable fvar) {
		assert(fvar != null);
		int hash = fvar.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof VariableAtom && ((VariableAtom)a).getVariable() == fvar )
				return a;
		}
		Atom a = new VariableAtom(fvar);
		atomCache.put(hash,a);
		return a;
	}
	public Atom atom(PredicateSymbol pred, Term... parameters) {
		assert(pred != null && parameters.length == pred.getParameterCount());
		int hash = Arrays.hashCode(parameters) + pred.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof PredicateAtom ) {
				PredicateAtom pa = (PredicateAtom)a;
				if( pred == pa.getPredicate() && Arrays.equals(parameters,pa.getParameters()) )
					return pa;
			}
		}
		PredicateAtom pa = new PredicateAtom(pred, parameters);
		atomCache.put(hash,pa);
		return pa;
	}
	public void createAxiom(Formula f) {
		axioms.add(f);
	}
	/**
	 * Create a formula variable with the given name.
	 * @param name   the variable name (without the leading $).
	 * @return a formula variable.
	 */
	public FormulaVariable createFormulaVariable(String name) {
		for (FormulaVariable fv : fvunify.iterateHashCode(name.hashCode())) {
			if( fv.getName().equals(name) )
				return fv;
		}
		FormulaVariable fv = new FormulaVariable(name);
		fvunify.put(name.hashCode(),fv);
		return fv;
	}
	/**
	 * Create a fresh formula variable that does not clash with any
	 * existing one.  
	 * @param prefix the prefix of the variable name.
	 * @return a fresh formula variable.
	 */
	public FormulaVariable createFreshFormulaVariable(String prefix) {
		return new FormulaVariable("!"+prefix+"!"+fvarctr++);
	}
	/**
	 * Create a fresh term variable that does not clash with any
	 * existing one.  
	 * @param prefix the prefix of the variable name (without the leading ?).
	 * @param sort   the sort of the variable.
	 * @return a fresh term variable.
	 */
	public TermVariable createFreshTermVariable(String prefix, Sort sort) {
		return new TermVariable("_b"+prefix+"_b"+tvarctr++, sort);
	}
	public FunctionSymbol createFunction(String name, Sort[] paramTypes, Sort resultType) {
		return createFunction(name, paramTypes, resultType, false);
	}
	FunctionSymbol createFunction(String name, Sort[] paramTypes, Sort resultType, boolean intern) {
		if (!intern && !checkQuotation(name))
			throw new IllegalArgumentException("Illegal SMTLIB name " + name);
		List<FunctionSymbol> fs = functions.get(name);
		if (fs == null) {
			fs = new ArrayList<FunctionSymbol>();
			functions.put(name, fs);
		} else {
		symbol_loop:
			for (FunctionSymbol f: fs) {
				if (f.getParameterCount() == paramTypes.length) {
					for (int i = 0; i < paramTypes.length; i++) {
						if (paramTypes[i] != f.getParameterSort(i))
							continue symbol_loop;
					}
					throw new IllegalArgumentException("Function "+name+" already exists.");
				}
			}
		}
		FunctionSymbol f = new FunctionSymbol(name, paramTypes, resultType, intern);
		fs.add(f);
		return f;
	}
	/**
	 * Creates temporary functions which are not dumped into files.
	 * @param name       Name of the temporary function
	 * @param paramTypes Sorts of the parameters
	 * @param resultType Sort of the result
	 * @return Temporary function symbol
	 */
	public FunctionSymbol createTempFunction(String name, Sort[] paramTypes, Sort resultType) {
		List<FunctionSymbol> fs = tempfs.get(name);
		if (fs == null) {
			fs = new ArrayList<FunctionSymbol>();
			tempfs.put(name, fs);
		} else {
		symbol_loop:
			for (FunctionSymbol f: fs) {
				if (f.getParameterCount() == paramTypes.length) {
					for (int i = 0; i < paramTypes.length; i++) {
						if (paramTypes[i] != f.getParameterSort(i))
							continue symbol_loop;
					}
					return f;
				}
			}
		}
		FunctionSymbol f = new FunctionSymbol(name, paramTypes, resultType, false);
		fs.add(f);
		return f;
	}
	public PredicateSymbol createTempPredicate(String name, Sort[] paramTypes) {
		List<PredicateSymbol> ps = tempps.get(name);
		if (ps == null) {
			ps = new ArrayList<PredicateSymbol>();
			tempps.put(name, ps);
		} else {
		symbol_loop:
			for (PredicateSymbol p: ps) {
				if (p.getParameterCount() == paramTypes.length) {
					for (int i = 0; i < paramTypes.length; i++) {
						if (paramTypes[i] != p.getParameterSort(i))
							continue symbol_loop;
					}
					return p;
				}
			}
		}
		PredicateSymbol p = new PredicateSymbol(name, paramTypes, false);
		ps.add(p);
		return p;
	}
	public void clearTemps() {
		tempfs.clear();
		tempps.clear();
	}
	private void createNumericOperators(Sort sort, boolean isRational) {
		createFunction("+", new Sort[] { sort, sort }, sort, true);
		createFunction("-", new Sort[] { sort, sort }, sort, true);
		if (isRational)
			createFunction("/", new Sort[] { sort, sort }, sort, true);
		createFunction("*", new Sort[] { sort, sort }, sort, true);
		if (logic.contains("LIRA"))
			createFunction("-", new Sort[] { sort }, sort, true);
		else
			createFunction("~", new Sort[] { sort }, sort, true);
		createPredicate(">", new Sort[] { sort, sort }, true);
		createPredicate(">=", new Sort[] { sort, sort }, true);
		createPredicate("<", new Sort[] { sort, sort }, true);
		createPredicate("<=", new Sort[] { sort, sort }, true);
	}
	public PredicateSymbol createPredicate(String name, Sort[] paramTypes) {
		return createPredicate(name, paramTypes, false);
	}
	public PredicateSymbol createPredicate(String name, Sort[] paramTypes, boolean intern) {
		if (!intern && !checkQuotation(name))
			throw new IllegalArgumentException("Illegal SMTLIB name " + name);
		List<PredicateSymbol> ps = predicates.get(name);
		if (ps == null) {
			ps = new ArrayList<PredicateSymbol>();
			predicates.put(name, ps);
		} else {
		symbol_loop:
			for (PredicateSymbol p: ps) {
				if (p.getParameterCount() == paramTypes.length) {
					for (int i = 0; i < paramTypes.length; i++) {
						if (paramTypes[i] != p.getParameterSort(i))
							continue symbol_loop;
					}
					throw new IllegalArgumentException("Predicate "+name+" already exists.");
				}
			}
		}
		PredicateSymbol p = new PredicateSymbol(name, paramTypes, intern);
		ps.add(p);
		return p;
	}
	public Sort createSort(String name) {
		return createSort(name, false);
	}
	Sort createSort(String id, boolean intern) {
		if (sorts.containsKey(id))
			throw new IllegalArgumentException("Sort "+id+" already exists.");
		Sort sort = new Sort(id, intern);
		sorts.put(id, sort);
		return sort;
	}
	/**
	 * Create a term variable with the given name and sort.
	 * @param name   the variable name.
	 * @param sort   the sort of the variable.
	 * @return a term variable.
	 */
	public TermVariable createTermVariable(String name,Sort sort) {
		// Hack for nativeZ3: sort == null ==> new TermVariable
		if( sort == null )
			return new TermVariable(name,sort);
		int hash = name.hashCode() ^ sort.hashCode();
		for (TermVariable tv : tvunify.iterateHashCode(hash)) {
			if( tv.getSort().equals(sort) && tv.getName().equals(name) )
				return tv;
		}
		TermVariable tv = new TermVariable(name,sort);
		tvunify.put(hash,tv);
		return tv;
	}
	public Atom distinct(Term... terms)
	{
		if (terms.length < 2)
			throw new IllegalArgumentException(
					"At least two terms must be distinct");
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() != terms.length)
			// We had something like (distinct ... a ... a ...)
			return Atom.FALSE;
		int hash = 0;
		for( Term t : terms )
			hash += t.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof DistinctAtom ) {
				DistinctAtom ea = (DistinctAtom)a;
				HashSet<Term> eaparams = new HashSet<Term>(Arrays.asList(ea.getTerms()));
				if( params.equals(eaparams) )
					return ea;
			}
		}
		DistinctAtom ea = new DistinctAtom(terms);
		atomCache.put(hash,ea);
		return ea;
	}
	@SuppressWarnings("unused")
	private Atom distinctz3(Term... terms)
	{
		int hash = 0;
		for( Term t : terms )
			hash += t.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof DistinctAtom ) {
				DistinctAtom ea = (DistinctAtom)a;
				if( Arrays.equals(terms,ea.getTerms()) )
					return ea;
			}
		}
		DistinctAtom ea = new DistinctAtom(terms);
		atomCache.put(hash,ea);
		return ea;
	}
	public void dumpBenchmark(PrintWriter pw, Formula formula) {
		pw.println("(benchmark stalin");
		pw.println("   :logic "+logic);
		for (Sort s: sorts.values()) {
			if (!s.isIntern())
				pw.println("   :extrasorts ("+s+")");
		}
		pw.print("   :extrapreds (");
		for (List<PredicateSymbol> ps: predicates.values()) {
			for (PredicateSymbol p : ps) {
				if (!p.isIntern())
					pw.print(p+" ");
			}
		}
		pw.println(")");
		pw.print("   :extrafuns (");
		for (List<FunctionSymbol> fs: functions.values()) {
			for (FunctionSymbol f : fs) {
				if (!f.isIntern())
					pw.print(f+" ");
			}
		}
		pw.println(")");
		
		for (Formula f: axioms) {
			pw.println("   :assumption "+f);
		}
		pw.println("   :formula "+formula);
		pw.println(")");
	}
	public void dumpInterpolationBenchmark(PrintWriter pw, Formula[] formulae) {
		pw.println("(benchmark stalininterpolation");
		pw.println("   :logic "+logic);
		for (Sort s: sorts.values()) {
			if (!s.isIntern())
				pw.println("   :extrasorts ("+s+")");
		}
		pw.print("   :extrapreds (");
		for (List<PredicateSymbol> ps: predicates.values()) {
			for (PredicateSymbol p : ps) {
				if (!p.isIntern())
					pw.print(p+" ");
			}
		}
		pw.println(")");
		pw.print("   :extrafuns (");
		for (List<FunctionSymbol> fs: functions.values()) {
			for (FunctionSymbol f : fs) {
				if (!f.isIntern())
					pw.print(f+" ");
			}
		}
		pw.println(")");
		
		for (Formula f: axioms) {
			pw.println("   :assumption "+f);
		}
		pw.println(":notes \"Interpolation Problem starts here\"");
		int i = 0;
		for( ; i < formulae.length - 1; ++i )
			pw.println("   :assumption "+formulae[i]);
		pw.println("   :formula "+formulae[i]);
		pw.println(")");
	}
	public Atom equals(Term... terms)
	{
		if (terms.length < 2)
			throw new IllegalArgumentException(
					"At least two terms must be equal");
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() == 1)
			// We had (= a a ... a)
			return Atom.TRUE;
		int hash = 0;
		for( Term t : terms )
			hash += t.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof EqualsAtom ) {
				EqualsAtom ea = (EqualsAtom)a;
				HashSet<Term> eaparams = new HashSet<Term>(Arrays.asList(ea.getTerms()));
				if( params.equals(eaparams) )
					return ea;
			}
		}
		EqualsAtom ea = new EqualsAtom(terms);
		atomCache.put(hash,ea);
		return ea;
	}
	@SuppressWarnings("unused")
	private Atom equalsz3(Term... terms)
	{
		int hash = 0;
		for( Term t : terms )
			hash += t.hashCode();
		for (Atom a : atomCache.iterateHashCode(hash)) {
			if( a instanceof EqualsAtom ) {
				EqualsAtom ea = (EqualsAtom)a;
				if( Arrays.equals(terms,ea.getTerms()) )
					return ea;
			}
		}
		EqualsAtom ea = new EqualsAtom(terms);
		atomCache.put(hash,ea);
		return ea;
	}
	public Formula exists(TermVariable[] vars, Formula f)
	{
		return exists(vars, f, new SMTLibBase[0][]);
	}
	public Formula exists(TermVariable[] vars, Formula f, SMTLibBase[][] triggers)
	{
		if (vars.length < 1)
			throw new IllegalArgumentException("No variable bound by quantifier");
		if (f == Atom.TRUE || f == Atom.FALSE)
			return f;
		int hash = Arrays.hashCode(vars) ^ f.hashCode() ^ Arrays.deepHashCode(triggers) + QuantifiedFormula.EXISTS;
		for (QuantifiedFormula qf : qfCache.iterateHashCode(hash)) {
			if( qf.getQuantifier() == QuantifiedFormula.EXISTS && Arrays.equals(vars,qf.getVariables()) && Arrays.deepEquals(triggers,qf.getTriggers()) )
				return qf;
		}
		QuantifiedFormula qf = new QuantifiedFormula(QuantifiedFormula.EXISTS, vars, f, triggers);
		qfCache.put(hash,qf);
		return qf;
	}
	public Formula flet(FormulaVariable fvar, Formula value, Formula subform) {
		if (subform == Atom.TRUE || subform == Atom.FALSE)
			return subform;
		int hash = fvar.hashCode() ^ value.hashCode() ^ subform.hashCode();
		for (FletFormula ff : fletCache.iterateHashCode(hash)) {
			if( ff.getVariable() == fvar && ff.getValue() == value && ff.getSubFormula() == subform )
				return ff;
		}
		FletFormula ff = new FletFormula(fvar, value, subform);
		fletCache.put(hash,ff);
		return ff;
	}
	public Formula forall(TermVariable[] vars, Formula f)
	{
		return forall(vars, f, new SMTLibBase[0][]);
	}
	
	public Formula forall(TermVariable[] vars, Formula f, SMTLibBase[][] triggers)
	{
		if (vars.length < 1)
			throw new IllegalArgumentException("No variable bound by quantifier");
		if (f == Atom.TRUE || f == Atom.FALSE)
			return f;
		int hash = Arrays.hashCode(vars) ^ f.hashCode() ^ Arrays.deepHashCode(triggers) + QuantifiedFormula.FORALL;
		for (QuantifiedFormula qf : qfCache.iterateHashCode(hash)) {
			if( qf.getQuantifier() == QuantifiedFormula.FORALL && Arrays.equals(vars,qf.getVariables()) && Arrays.deepEquals(triggers,qf.getTriggers()) )
				return qf;
		}
		QuantifiedFormula qf = new QuantifiedFormula(QuantifiedFormula.FORALL, vars, f, triggers);
		qfCache.put(hash,qf);
		return qf;
	}
	public Collection<Formula> getAxioms() {
		return axioms;
	}
	public FunctionSymbol getFunction(String name, Sort... paramTypes) {
		List<FunctionSymbol> fs = functions.get(name);
		if (fs == null)
			return null;
	symbol_loop:
		for (FunctionSymbol f: fs) {
			if (f.getParameterCount() == paramTypes.length) {
				for (int i = 0; i < paramTypes.length; i++) {
					if (paramTypes[i] != f.getParameterSort(i))
						continue symbol_loop;
				}
				return f;
			}
		}
		return null;
	}
	public Collection<FunctionSymbol> getFunctions() {
		int s = 0;
		final Collection<List<FunctionSymbol>> funcs = functions.values();
		for (List<FunctionSymbol> l: funcs)
			s += l.size();
		final int size = s;
		return new AbstractCollection<FunctionSymbol>() {
			@SuppressWarnings("unchecked")
			public Iterator<FunctionSymbol> iterator() {
				return new Iterator<FunctionSymbol>() {
					Iterator<List<FunctionSymbol>> iouter = funcs.iterator();
					Iterator<FunctionSymbol> iinner = 
						Collections.EMPTY_SET.iterator();
					
					public boolean hasNext() {
						while (!iinner.hasNext() && iouter.hasNext())
							iinner = iouter.next().iterator();
						return iinner.hasNext();
					}
					public FunctionSymbol next() {
						while (!iinner.hasNext() && iouter.hasNext())
							iinner = iouter.next().iterator();
						return iinner.next();
					}
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
			}

			public int size() {
				return size;
			}
		};
	}
	public PredicateSymbol getPredicate(String name, Sort... paramTypes) {
		List<PredicateSymbol> ps = predicates.get(name);
		if (ps == null)
			return null;
	symbol_loop:
		for (PredicateSymbol p: ps) {
			if (p.getParameterCount() == paramTypes.length) {
				for (int i = 0; i < paramTypes.length; i++) {
					if (paramTypes[i] != p.getParameterSort(i))
						continue symbol_loop;
				}
				return p;
			}
		}
		return null;
	}
	public Collection<PredicateSymbol> getPredicates() {
		int s = 0;
		final Collection<List<PredicateSymbol>> preds = predicates.values();
		for (List<PredicateSymbol> l: preds)
			s += l.size();
		final int size = s;
		return new AbstractCollection<PredicateSymbol>() {
			@SuppressWarnings("unchecked")
			public Iterator<PredicateSymbol> iterator() {
				return new Iterator<PredicateSymbol>() {
					Iterator<List<PredicateSymbol>> iouter = preds.iterator();
					Iterator<PredicateSymbol> iinner = 
						Collections.EMPTY_SET.iterator();
					
					public boolean hasNext() {
						while (!iinner.hasNext() && iouter.hasNext())
							iinner = iouter.next().iterator();
						return iinner.hasNext();
					}
					public PredicateSymbol next() {
						while (!iinner.hasNext() && iouter.hasNext())
							iinner = iouter.next().iterator();
						return iinner.next();
					}
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
			}

			public int size() {
				return size;
			}
		};
	}
	public Sort getSort(String id) {
		return sorts.get(id);
	}
	public Collection<Sort> getSorts() {
		return sorts.values();
	}
	public Formula iff(Formula f, Formula g)
	{ 
		if (f == Atom.TRUE) return g;
		if (g == Atom.TRUE) return f;
		if (f == Atom.FALSE) return not(g);
		if (g == Atom.FALSE) return not(f);
		if( f == g ) return Atom.TRUE;
		int hash = hashConnectedFormula(ConnectedFormula.IFF,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.IFF && (
					(conf.getLhs() == f && conf.getRhs() == g) || (conf.getLhs() == g && conf.getRhs() == f)) )
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.IFF, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	@SuppressWarnings("unused")
	private Formula iffz3(Formula lhs,Formula rhs) {
		int hash = hashConnectedFormula(ConnectedFormula.IFF, lhs, rhs);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.IFF && lhs == conf.getLhs() && rhs == conf.getRhs() )
				return conf;
		}
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.IFF,lhs,rhs);
		conCache.put(hash,conf);
		return conf;
	}
	public Formula ifthenelse(Formula f, Formula t, Formula e)
	{
		if (f == Atom.TRUE)  return t;
		if (f == Atom.FALSE) return e;
		int hash = f.hashCode() ^ t.hashCode() ^ e.hashCode();
		for (ITEFormula ite : iteCache.iterateHashCode(hash)) {
			if( ite.getCondition() == f && ite.getTrueCase() == t && ite.getFalseCase() == e )
				return ite;
		}
		ITEFormula ite = new ITEFormula(f, t, e);
		iteCache.put(hash,ite);
		return ite;
	}
	@SuppressWarnings("unused")
	private Formula ifthenelsez3(Formula f, Formula t, Formula e)
	{
		int hash = f.hashCode() ^ t.hashCode() ^ e.hashCode();
		for (ITEFormula ite : iteCache.iterateHashCode(hash)) {
			if( ite.getCondition() == f && ite.getTrueCase() == t && ite.getFalseCase() == e )
				return ite;
		}
		ITEFormula ite = new ITEFormula(f, t, e);
		iteCache.put(hash,ite);
		return ite;
	}
	public Formula implies(Formula f, Formula g)
	{ 
		if (g == Atom.TRUE || f == Atom.TRUE) return g;
		if (f == Atom.FALSE) return Atom.TRUE;
		if (g == Atom.FALSE) return not(f);
		if( f == g ) return Atom.TRUE;
		if (g instanceof ConnectedFormula &&
				((ConnectedFormula)g).getConnector() == ConnectedFormula.IMPLIES) {
			return implies(and(f, ((ConnectedFormula) g).getLhs()), ((ConnectedFormula) g).getRhs());
		}
		int hash = hashConnectedFormula(ConnectedFormula.IMPLIES,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.IMPLIES && conf.getLhs() == f && conf.getRhs() == g)
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.IMPLIES, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	@SuppressWarnings("unused")
	private Formula impliesz3(Formula f, Formula g)
	{
		int hash = hashConnectedFormula(ConnectedFormula.IMPLIES,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.IMPLIES && conf.getLhs() == f && conf.getRhs() == g)
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.IMPLIES, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	public Term ite(Formula f, Term t, Term e)
	{
		if (f == Atom.TRUE)  return t;
		if (f == Atom.FALSE) return e;
		int hash = f.hashCode() ^ t.hashCode() ^ e.hashCode();
		for (Term cur : termCache.iterateHashCode(hash)) {
			if( cur instanceof ITETerm ) {
				ITETerm ite = (ITETerm)cur;
				if( f == ite.getCondition() && t == ite.getTrueCase() && e == ite.getFalseCase() )
					return ite;
			}
		}
		ITETerm ite = new ITETerm(f, t, e);
		termCache.put(hash,ite);
		return ite;
	}
	@SuppressWarnings("unused")
	private Term itez3(Formula f, Term t, Term e)
	{
		int hash = f.hashCode() ^ t.hashCode() ^ e.hashCode();
		for (Term cur : termCache.iterateHashCode(hash)) {
			if( cur instanceof ITETerm ) {
				ITETerm ite = (ITETerm)cur;
				if( f == ite.getCondition() && t == ite.getTrueCase() && e == ite.getFalseCase() )
					return ite;
			}
		}
		ITETerm ite = new ITETerm(f, t, e);
		termCache.put(hash,ite);
		return ite;
	}
	
	public Formula let(TermVariable var, Term value, Formula subform) {
		if (subform == Atom.TRUE || subform == Atom.FALSE)
			return subform;
		int hash = var.hashCode() ^ value.hashCode() ^ subform.hashCode();
		for (LetFormula lf : letCache.iterateHashCode(hash)) {
			if( lf.getVariable() == var && lf.getValue() == value && lf.getSubFormula() == subform )
				return lf;
		}
		LetFormula lf = new LetFormula(var, value, subform);
		letCache.put(hash,lf);
		return lf;
	}

	public Formula not(Formula f)
	{
		if (f == Atom.TRUE) return Atom.FALSE;
		if (f == Atom.FALSE) return Atom.TRUE;
		if (f instanceof NegatedFormula)
			return ((NegatedFormula) f).getSubFormula();
		return notz3(f);
	}

	/**
	 * Build negated formula, without any optimizations.
	 * This formula is also used by the z3 native smt-interface.
	 * DO NOT REMOVE IT. 
	 * @param f the formula to negate.
	 * @return the negated formula.
	 */
	private Formula notz3(Formula f)
	{
		int hash = f.hashCode();
		for (NegatedFormula fneg : notCache.iterateHashCode(hash)) {
			if (fneg.getSubFormula() == f)
				return fneg;
		}
		NegatedFormula fneg = new NegatedFormula(f);
		notCache.put(hash, fneg);
		return fneg;
	}
	
	public Term numeral(BigInteger num) {
		int hash = num.hashCode();
		for (Term t : termCache.iterateHashCode(hash) ) {
			if( t instanceof NumeralTerm ) {
				NumeralTerm nt = (NumeralTerm)t;
				if( nt.getSort() == numericSort && num.equals(nt.getNumeral()) )
					return  nt;
			}
		}
		NumeralTerm nt = new NumeralTerm(num,numericSort);
		termCache.put(hash,nt);
		return nt;
	}
	
	public Term numeral(String num) {
		return numeral(new BigInteger(num));
	}

	// Z3 internals: Do not simplify or respect commutativity
	public Formula oeq(Formula f,Formula g) {
		int hash = hashConnectedFormula(ConnectedFormula.OEQ, f, g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.OEQ && (conf.getLhs() == f && conf.getRhs() == g) )
				return conf;
		}		
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.OEQ,f,g);
		conCache.put(hash, conf);
		return conf;
	}

	public Formula internalOr(Formula f, Formula g)
	{ 
		int hash = hashConnectedFormula(ConnectedFormula.OR,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.OR && (
					(conf.getLhs() == f && conf.getRhs() == g) || (conf.getLhs() == g && conf.getRhs() == f)) )
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.OR, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	public Formula or(Formula f, Formula g)
	{ 
		if (g == Atom.FALSE || f == Atom.TRUE) return f;
		if (g == Atom.TRUE || f == Atom.FALSE) return g;
		if( f == g ) return f;
		HashSet<Formula> seen = new HashSet<Formula>();
		Formula rhs = g;
		while (rhs instanceof ConnectedFormula &&
				((ConnectedFormula)g).getConnector() == ConnectedFormula.OR) {
			ConnectedFormula cf = (ConnectedFormula) rhs;
			seen.add(cf.getLhs());
			rhs = cf.getRhs();
		}
		seen.add(rhs);
		/* Normalize to right-assoc */
		Stack<Formula> fcomponents = new Stack<Formula>();
		while (f instanceof ConnectedFormula &&
				((ConnectedFormula)f).getConnector() == ConnectedFormula.OR) {
			fcomponents.push(((ConnectedFormula) f).getLhs());
			f = ((ConnectedFormula) f).getRhs();
		}
		Formula result = g;
		if (seen.add(f))
			result = internalOr(f, result);
		while (fcomponents.size() > 0) {
			Formula subf = fcomponents.pop(); 
			if (seen.add(subf))
				result = internalOr(subf, result);
		}
		return result;
	}

	@SuppressWarnings("unused")
	private Formula orz3(Formula lhs,Formula rhs) {
		int hash = hashConnectedFormula(ConnectedFormula.OR, lhs, rhs);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.OR && lhs == conf.getLhs() && rhs == conf.getRhs() )
				return conf;
		}
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.OR,lhs,rhs);
		conCache.put(hash,conf);
		return conf;
	}
	// Assumes gcd(num,denom) == BigInteger.ONE || gcd(num,denom) == BigInteger.ZERO
	public Term rational(BigInteger num,BigInteger denom) {
		int hash = num.hashCode() ^ denom.hashCode();
		for (Term t : termCache.iterateHashCode(hash)) {
			if( t instanceof RationalTerm ) {
				RationalTerm rt = (RationalTerm)t;
				if( rt.getSort() == rationalSort && num.equals(rt.getNumerator()) && denom.equals(rt.getDenominator()) )
					return  rt;
			}
		}
		RationalTerm rt = new RationalTerm(num,denom,rationalSort);
		termCache.put(hash,rt);
		return rt;
	}
	
	public Term rational(String num) {
		int dotPos = num.indexOf(".");
		BigInteger numerator = new BigInteger(num.substring(0, dotPos)+ num.substring(dotPos+1));
		BigInteger denominator = BigInteger.ONE;
		for (int i = num.length() - dotPos - 1; i > 0; i--)
			denominator = denominator.multiply(BigInteger.TEN);
		BigInteger gcd = numerator.gcd(denominator);
		numerator = numerator.divide(gcd);
		denominator = denominator.divide(gcd);
		int hash = numerator.hashCode() ^ denominator.hashCode();
		for (Term t : termCache.iterateHashCode(hash)) {
			if( t instanceof RationalTerm ) {
				RationalTerm rt = (RationalTerm)t;
				if( rt.getSort() == rationalSort && numerator.equals(rt.getNumerator()) && denominator.equals(rt.getDenominator()) )
					return  rt;
			}
		}
		RationalTerm rt = new RationalTerm(numerator,denominator,rationalSort);
		termCache.put(hash,rt);
		return rt;
	}
	
	public Term rational(String num,String denom) {
		BigInteger numerator = new BigInteger(num);
		BigInteger denominator = denom != null ? new BigInteger(denom) : BigInteger.ONE;
		BigInteger gcd = numerator.gcd(denominator);
		numerator = numerator.divide(gcd);
		denominator = denominator.divide(gcd);
		int hash = numerator.hashCode() ^ denominator.hashCode();
		for (Term t : termCache.iterateHashCode(hash)) {
			if( t instanceof RationalTerm ) {
				RationalTerm rt = (RationalTerm)t;
				if( rt.getSort() == rationalSort && numerator.equals(rt.getNumerator()) && denominator.equals(rt.getDenominator()) )
					return  rt;
			}
		}
		RationalTerm rt = new RationalTerm(numerator,denominator,rationalSort);
		termCache.put(hash,rt);
		return rt;
	}

	public ApplicationTerm term(FunctionSymbol func, Term... parameters) {
		assert(func != null && parameters.length == func.getParameterCount());
		int hash = func.hashCode() ^ Arrays.hashCode(parameters);
		for (Term t : termCache.iterateHashCode(hash)) {
			if( t instanceof ApplicationTerm ) {
				ApplicationTerm app = (ApplicationTerm)t;
				if( func == app.getFunction() && Arrays.equals(app.getParameters(),parameters) )
					return app;
			}
		}
		ApplicationTerm app = new ApplicationTerm(func, parameters);
		termCache.put(hash,app);
		return app;
	}

	public Term term(TermVariable var) {
		// TermVariable unifies this! 
		return var.createTerm();
	}
	public Formula xor(Formula f, Formula g)
	{ 
		if (f == Atom.TRUE) return not(g);
		if (g == Atom.TRUE) return not(f);
		if (f == Atom.FALSE) return g;
		if (g == Atom.FALSE) return f;
		if( f == g ) return Atom.FALSE;
		int hash = hashConnectedFormula(ConnectedFormula.XOR,f,g);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.XOR && (
					(conf.getLhs() == f && conf.getRhs() == g) || (conf.getLhs() == g && conf.getRhs() == f)) )
				return conf;
		} 
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.XOR, f, g);
		conCache.put(hash,conf);
		return conf;
	}
	@SuppressWarnings("unused")
	private Formula xorz3(Formula lhs,Formula rhs) {
		int hash = hashConnectedFormula(ConnectedFormula.XOR, lhs, rhs);
		for (ConnectedFormula conf : conCache.iterateHashCode(hash)) {
			if( conf.getConnector() == ConnectedFormula.XOR && lhs == conf.getLhs() && rhs == conf.getRhs() )
				return conf;
		}
		ConnectedFormula conf = new ConnectedFormula(ConnectedFormula.XOR,lhs,rhs);
		conCache.put(hash,conf);
		return conf;
	}
	public static boolean checkQuotation(String name) {
		for (int i = 0; i < name.length(); ++i) {
			switch (name.charAt(i)) {
			case '\'':
			case '!':
			case '$':
			case '~':
			case '?':
			case '#':
				return false;
			default:
				char c = name.charAt(i);
				if (!(('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || 
						('0' <= c && c <= '9') || c == '_' || c == '.'))
					return false;
				break;
			}
		}
		return true;
	}
}
