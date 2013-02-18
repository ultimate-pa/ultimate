package local.stalin.smt.convert;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.DistinctAtom;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.FletFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.LetFormula;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.RationalTerm;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableAtom;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.NamedAtom;
import local.stalin.smt.hack.GroundMap;
import local.stalin.smt.hack.Instantiation;
import local.stalin.smt.hack.SymbolRange;
import local.stalin.smt.theory.cclosure.CCTerm;
import local.stalin.smt.theory.cclosure.CClosure;
import local.stalin.smt.theory.cclosure.EqualityAtom;
import local.stalin.smt.theory.linar.AffinTerm;
import local.stalin.smt.theory.linar.IntLinArSolve;
import local.stalin.smt.theory.linar.LinArSolve;
import local.stalin.smt.theory.linar.LinVar;
import local.stalin.smt.theory.linar.Rational;
import local.stalin.smt.util.DebugMessage;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

public class ConvertFormula {
	private Logger logger;

	public final static int OR = ConnectedFormula.OR;
	public final static int AND = ConnectedFormula.AND;
	DPLLEngine dpllEngine;
	CClosure cclosure;
	LinArSolve linarSolver;
	IntLinArSolve intLinarSolver;

	int numClauses, numAtoms;

	FlatFormula TRUE = new FlatFormula(this);
	FlatFormula FALSE = new FlatFormula(this);
	HashMap<Literal, LiteralFormula> literalFFs = new HashMap<Literal, LiteralFormula>();
	HashMap<Set<FlatFormula>, FlatFormula> clauseFFs = new HashMap<Set<FlatFormula>, FlatFormula>();
	HashMap<Object, FlatTerm> symbolicTerms = new HashMap<Object, FlatTerm>();

	HashMap<Formula, FlatFormula> formulaCache = new HashMap<Formula, FlatFormula>();

	/**
	 * This class represents a converted term.  
	 * The objects of this class only live for a short time. They
	 * are created by convertTerm and are freed when the caller
	 * exits.  In particular they are no long alive when a formula
	 * is completely processed.
	 * 
	 * A term must either be a CCTerm, in which case the ccTerm
	 * member is non-null, or a AffinTerm, in which case the
	 * linSum member is non-null.
	 * 
	 * Every term can appear in any of the
	 * theories, but it is only added to the theory if necessary.
	 * A term may also be temporary and then it is not added to
	 * any theory at all.
	 * If a term belongs to more than one theory it is also 
	 * included in the global shared term array.
	 * 
	 * @author hoenicke
	 */
	class FlatTerm {
		/**
		 * The smt term this flat term corresponds to.
		 * This is not always set, e.g. for affin terms.
		 */
		Term smtTerm;
		/**
		 * The congruence closure term this terms lives in.
		 * This is only created for non-trivial function 
		 * application terms and when getCCTerm is called.
		 */
		CCTerm ccTerm;
		/**
		 * The affin term if this term is a linear sum.  This
		 * is created on the fly if getLinSum is called.  In
		 * that case a new linear variable may be registered
		 * in that theory.
		 */
		AffinTerm linSum;
		/**
		 * List of all term variables contained in this flat term.
		 */
		Set<TermVariable> termVariables = null;

		public void addTermVariable(TermVariable tv) {
			if (termVariables == null)
				termVariables = new HashSet<TermVariable>();
			termVariables.add(tv);
		}
		
		public Set<TermVariable> getTermVariables() {
			return termVariables;
		}
		
		public void combineTermVariableLists(FlatTerm other) {
			Set<TermVariable> othertvs = other.getTermVariables();
			if (othertvs != null) {
				if (termVariables == null)
					termVariables = new HashSet<TermVariable>();
				termVariables.addAll(othertvs);
			}
		}
		
		public CCTerm getCCTerm(int formNumber) {
			if (ccTerm == null) {
				ccTerm = linsumTerms.get(linSum);
				if (ccTerm == null) {
					ccTerm = cclosure.createAnonTerm(/*smtTerm*/linSum.toSMTLib(dpllEngine.getSMTTheory()));
//					if (!(smtTerm instanceof VariableTerm))// FIXME: This seems to be the problem line
						linsumTerms.put(linSum, ccTerm);
				}
				if (!linSum.isConstant())
					ccTerm.occursIn(linSum.getFirstFormulaNr());
				ccTerm.occursIn(formNumber);
			}
			return ccTerm;
		}

		public boolean isRational() {
			return linSum != null && linSum.isConstant();
		}

		public Rational getRational() {
			return linSum.getConstant();
		}

		public boolean isIntegral() {
			return smtTerm.getSort().getName().equals("Int");
		}

		public AffinTerm getLinSum(int formNumber) {
			if (linSum == null) {
				LinVar linVar = linarVariables.get(ccTerm);
				if (linVar == null) {
					boolean isint = isIntegral();
					LinArSolve laTheory;
					if (isIntegral()) {
						if (intLinarSolver == null) {
							intLinarSolver = new IntLinArSolve(dpllEngine);
							dpllEngine.addTheory(intLinarSolver);
						}
						laTheory = intLinarSolver;
					} else {
						if (linarSolver == null) {
							linarSolver = new LinArSolve(dpllEngine);
							dpllEngine.addTheory(linarSolver);
						}
						laTheory = linarSolver;
					}
					linVar = laTheory.addVar(smtTerm, isint);
					linVar.occursIn(ccTerm.getFirstFormula());
					linVar.occursIn(Math.max(formNumber,ccTerm.getLastFormula()));
					linarVariables.put(ccTerm, linVar);
				}
				linSum = new AffinTerm(linVar);
//				if (!(smtTerm instanceof VariableTerm))//FIXME: This seems to be the problem line!!!
					linsumTerms.put(linSum, ccTerm);
			}
			return linSum;
		}

		public FlatTerm(CCTerm t, Term smtTerm, int formNumber) {
			this.smtTerm = smtTerm;
			this.ccTerm = t;
			t.occursIn(formNumber);
			if (linarVariables.containsKey(t))
				linarVariables.get(t).occursIn(formNumber);
		}

		public FlatTerm(AffinTerm sum, Term smtTerm) {
			this.smtTerm = smtTerm;
			linSum = sum;
		}

		public FlatTerm(Rational rat, Term smtTerm) {
			this.smtTerm = smtTerm;
			linSum = new AffinTerm(rat, isIntegral());
		}

		public boolean isLinSum() {
			return linSum != null;
		}

		public boolean isCCTerm() {
			return ccTerm != null;
		}
	}

	private FlatTerm createFlat(CCTerm term, Term smtTerm, int formNumber) {
		return new FlatTerm(term, smtTerm, formNumber);
	}

	private FlatTerm createFlat(Rational rationalNumber, Term smtTerm) {
		return new FlatTerm(rationalNumber, smtTerm);
	}

	private FlatTerm createFlat(AffinTerm linsum, Term smtTerm) {
		return new FlatTerm(linsum, smtTerm);
	}

	LiteralFormula createLiteralFormula(Formula smtFormula, Literal lit) {
		LiteralFormula result = literalFFs.get(lit);
		if (result == null) {
			result = new LiteralFormula(this, smtFormula, lit);
			literalFFs.put(lit, result);
			Formula tmp = lit.getSMTFormula(dpllEngine.getSMTTheory());
			final HashSet<TermVariable> supportset = new HashSet<TermVariable>();
			FormulaWalker fw = new FormulaWalker(new SymbolVisitor() {

				HashSet<TermVariable> masked = new HashSet<TermVariable>();
				
				@Override
				public void done(Term input) {	}

				@Override
				public void done(PredicateAtom pa) {}

				@Override
				public void endscope(TermVariable tv) {
					masked.remove(tv);
				}

				@Override
				public void endscopes(TermVariable[] tvs) {
					for (TermVariable tv : tvs)
						masked.remove(tv);
				}

				@Override
				public void let(TermVariable tv, Term mval) {
					masked.add(tv);
				}

				@Override
				public Formula predicate(PredicateAtom pa) {
					return null;
				}

				@Override
				public void quantifier(TermVariable[] tvs) {
					for (TermVariable tv : tvs)
						masked.add(tv);
				}

				@Override
				public Term term(Term input) {
					if (input instanceof ApplicationTerm || 
							input instanceof ITETerm)
					return null;
					if (input instanceof VariableTerm)
						supportset.add(((VariableTerm)input).getVariable());
					return input;
				}

				@Override
				public boolean unflet() {
					return false;
				}

				@Override
				public boolean unlet() {
					return false;
				}
				
			},dpllEngine.getSMTTheory());
			fw.process(tmp);
			result.termVariables = supportset;
			lit.getAtom().setInstantiationVariables(supportset);
		}
		return result;
	}

	private FlatFormula createClauseFormula(Set<FlatFormula> subforms) {
		if (subforms.size() == 0)
			return FALSE;
		if (subforms.size() == 1)
			return subforms.iterator().next();
		FlatFormula result = clauseFFs.get(subforms);
		if (result == null) {
			result = new ClauseFormula(this, subforms);
			clauseFFs.put(subforms, result);
		}
		return result;
	}

	private FlatFormula createIfThenElse(FlatFormula cond,
			FlatFormula thenForm, FlatFormula elseForm) {
		if (cond.isTrue())
			return thenForm;
		if (cond.isFalse())
			return elseForm;
		if (thenForm.isTrue())
			return convertDisjunction(cond, elseForm);
		if (thenForm.isFalse())
			return convertDisjunction(cond, elseForm.negate()).negate();
		if (elseForm.isTrue())
			return convertDisjunction(cond.negate(), thenForm);
		if (elseForm.isFalse())
			return convertDisjunction(cond.negate(), thenForm.negate())
					.negate();
		return new IfThenElseFormula(this, cond, thenForm, elseForm);
	}

	HashMap<CCTerm, LinVar> linarVariables = new HashMap<CCTerm, LinVar>();
	HashMap<AffinTerm, CCTerm> linsumTerms = new HashMap<AffinTerm, CCTerm>();

	HashMap<FormulaVariable, FlatFormula> fletTable = new HashMap<FormulaVariable, FlatFormula>();

	public void addClause(Literal[] literals,int formNumber) {
		assert(checkClauseSupportSet(literals));
		/* simplify clause by merging identical literals */
		HashSet<Literal> lits = new HashSet<Literal>();
		lits.addAll(Arrays.asList(literals));
		if (lits.size() != literals.length)
			literals = lits.toArray(new Literal[lits.size()]);
		
		/* check for trivial tautologies */
		for (Literal l : literals)
			if (lits.contains(l.negate()))
				return;
		
		dpllEngine.addFormulaClause(literals, formNumber);
		numClauses++;
		if (logger.isDebugEnabled())
			logger.debug("Adding clause: " + lits);
	}

	NamedAtom createAnonAtom(Formula smtFormula) {
		String name = "aux!" + numAtoms;
		NamedAtom atom = new NamedAtom(name, smtFormula);
		dpllEngine.addAtom(atom);
		numAtoms++;
		return atom;
	}

	private FlatTerm convertFuncTerm(ApplicationTerm f, int formNumber) {
		if (f.getFunction().getName().equals("+")
				&& f.getParameters().length == 2) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm arg1 = convertTerm(f.getParameters()[1], formNumber);
			FlatTerm result = createFlat(arg0.getLinSum(formNumber).add(arg1.getLinSum(formNumber)), f);
			result.combineTermVariableLists(arg0);
			result.combineTermVariableLists(arg1);
			return result;
		}
		else if (f.getFunction().getName().equals("-")
				&& f.getParameters().length == 2) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm arg1 = convertTerm(f.getParameters()[1], formNumber);
			FlatTerm result = createFlat(arg0.getLinSum(formNumber).add(arg1.getLinSum(formNumber).negate()), f);
			// TODO: ?x - ?x does not support ?x any longer...
			result.combineTermVariableLists(arg0);
			result.combineTermVariableLists(arg1);
			return result;
		}
		else if (f.getFunction().getName().equals("*")
				&& f.getParameters().length == 2) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm arg1 = convertTerm(f.getParameters()[1], formNumber);
			FlatTerm result = null;
			if (arg0.isRational())
				result = createFlat(arg1.getLinSum(formNumber).mul(arg0.getRational()), f);
			else if (arg1.isRational())
				result = createFlat(arg0.getLinSum(formNumber).mul(arg1.getRational()), f);
			if (result != null) {
				result.combineTermVariableLists(arg0);
				result.combineTermVariableLists(arg1);
				return result;
			}
		}
		else if (f.getFunction().getName().equals("/")
				&& f.getParameters().length == 2) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm arg1 = convertTerm(f.getParameters()[1], formNumber);
			if (arg1.isRational()) {
				FlatTerm result = createFlat(arg0.getLinSum(formNumber).div(arg1.getRational()), f);
				result.combineTermVariableLists(arg0);
				result.combineTermVariableLists(arg1);
				return result;
			}
		}
		if ((f.getFunction().getName().equals("~")
			 || f.getFunction().getName().equals("-"))
				&& f.getParameters().length == 1) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm result = createFlat(arg0.getLinSum(formNumber).negate(), f);
			result.termVariables = arg0.termVariables;
			return result;
		}
		CCTerm[] args = new CCTerm[f.getParameters().length];
		Set<TermVariable> supportset = null;
		for (int i = 0; i < args.length; i++) {
			FlatTerm ft = convertTerm(f.getParameters()[i], formNumber);
			// CCTerm t = ft.getDPLLTerm();
			if (ft.getTermVariables() != null && !ft.getTermVariables().isEmpty()) {
				if (supportset == null)
					supportset = new HashSet<TermVariable>();
				supportset.addAll(ft.getTermVariables());
			}
			args[i] = ft.getCCTerm(formNumber);
		}
		CCTerm term = cclosure.createFuncTerm(f.getFunction(), args);
		FlatTerm result = createFlat(term, cclosure.convertTermToSMT(term), formNumber);
		result.termVariables = supportset;
		return result;
	}

	private static int itectr = 0;

	private FlatTerm convertTerm(Term term, int formNumber) {
		if (term instanceof ApplicationTerm) {
			return convertFuncTerm((ApplicationTerm) term, formNumber);
		} else if (term instanceof ITETerm) {
			Set<TermVariable> supportset = new HashSet<TermVariable>();
			ITETerm ite = (ITETerm) term;
			String ites = "ite_b" + itectr++;
			FunctionSymbol func = dpllEngine.getSMTTheory().createFunction(
					ites, new Sort[0], term.getSort());
			CCTerm result = convertFuncTerm(dpllEngine.getSMTTheory().term(func), formNumber).ccTerm;
			FlatFormula cond = convertFormula(ite.getCondition(), formNumber);
			if (cond.termVariables != null)
				supportset.addAll(cond.termVariables);
			FlatFormula thenForm = createLiteralFormula(
					null, cclosure
							.createEquality(result, convertTerm(
									ite.getTrueCase(), formNumber).getCCTerm(formNumber)));
			if (thenForm.termVariables != null)
				supportset.addAll(thenForm.termVariables);
			FlatFormula elseForm = createLiteralFormula(
					null, cclosure
							.createEquality(result, convertTerm(
									ite.getFalseCase(), formNumber).getCCTerm(formNumber)));
			if (elseForm.termVariables != null)
				supportset.addAll(elseForm.termVariables);
			FlatFormula flatite = createIfThenElse(cond, thenForm, elseForm);
			if (!supportset.isEmpty())
				flatite.termVariables = supportset;
			flatite.addAsAxiom(formNumber);
			// TODO: do we need support on result as well???
			return createFlat(result, term, formNumber);
		} else if (term instanceof VariableTerm) {
			TermVariable tv = ((VariableTerm)term).getVariable();
			FlatTerm result = symbolicTerms.get(tv);
			if (result == null) {
				SymbolRange locality = GroundMap.singletonGroundMap().getLocality(tv);
				if (locality == null)
					throw new IllegalArgumentException("Variable " + term
							+ " undeclared");
				result = createFlat(cclosure.createTermVariableTerm(tv),term, formNumber);
				result.addTermVariable(tv);
			}
			return result;
		} else if (term instanceof NumeralTerm) {
			return createFlat(Rational.valueOf(((NumeralTerm) term).getNumeral(),
					BigInteger.ONE), term);
		} else if (term instanceof RationalTerm) {
			RationalTerm t = (RationalTerm) term;
			Rational rat = Rational.valueOf(t.getNumerator(), t.getDenominator());
			return createFlat(rat, term);
		} else {
			throw new IllegalArgumentException("Cannot handle: " + term);
		}
	}

	private Literal createLeq0Literal(AffinTerm linsum) {
		LinArSolve solver = linsum.isIntegral() 
			? intLinarSolver : linarSolver;
		return solver.generateConstraint(linsum, false); 
	}

	private FlatFormula createLeq0Formula(final AffinTerm linsum) {
		if (linsum.isConstant()) {
			return linsum.getConstant().compareTo(Rational.ZERO) <= 0 ? TRUE
					: FALSE;
		}
		return createLiteralFormula(null, createLeq0Literal(linsum));
	}

	private FlatFormula createEqualityFormula(FlatTerm t1, FlatTerm t2, int formNumber) {
		if ((!t1.isCCTerm() && !t1.isRational())
			|| (!t2.isCCTerm() && !t2.isRational())) {
			AffinTerm diff = t1.getLinSum(formNumber).add(t2.getLinSum(formNumber).negate());
			FlatFormula leq = createLeq0Formula(diff);
			FlatFormula geq = createLeq0Formula(diff.negate());
			return convertDisjunction(geq.negate(), leq.negate()).negate();
		}
		CCTerm cc1 = t1.getCCTerm(formNumber);
		CCTerm cc2 = t2.getCCTerm(formNumber);
		if (cc1 == cc2)
			return TRUE;
		Literal eqlit = cclosure.createEquality(cc1, cc2);
		return createLiteralFormula(null, eqlit);
	}

	private FlatFormula convertPredicate(PredicateAtom f, int formNumber) {
		if (f.getParameters().length == 2
				&& (f.getPredicate().getName().equals(">")
						|| f.getPredicate().getName().equals("<")
						|| f.getPredicate().getName().equals(">=") || f
						.getPredicate().getName().equals("<="))) {
			FlatTerm arg0 = convertTerm(f.getParameters()[0], formNumber);
			FlatTerm arg1 = convertTerm(f.getParameters()[1], formNumber);
			AffinTerm sum = arg0.getLinSum(formNumber).add(arg1.getLinSum(formNumber).negate());
			Set<TermVariable> supportset = new HashSet<TermVariable>();
			if (arg0.termVariables != null)
				supportset.addAll(arg0.termVariables);
			if (arg1.termVariables != null)
				supportset.addAll(arg1.termVariables);
			FlatFormula res;
			if (f.getPredicate().getName().equals(">"))
				res = createLeq0Formula(sum).negate();
			else if (f.getPredicate().getName().equals("<"))
				res = createLeq0Formula(sum.negate()).negate();
			else if (f.getPredicate().getName().equals(">="))
				res = createLeq0Formula(sum.negate());
			else
				/* if (f.getPredicate().getName().equals("<=")) */
				res = createLeq0Formula(sum);
			res.termVariables = supportset;
			return res;
		}
		CCTerm[] args = new CCTerm[f.getParameters().length];
		Set<TermVariable> supportset = new HashSet<TermVariable>();
		for (int i = 0; i < args.length; i++) {
			FlatTerm flatarg = convertTerm(f.getParameters()[i], formNumber);
			if (flatarg.termVariables != null)
				supportset.addAll(flatarg.termVariables);
			args[i] = flatarg.getCCTerm(formNumber);
		}
		Literal atom = cclosure.createPredAtom(f.getPredicate(), args, formNumber);
		FlatFormula res = createLiteralFormula(f, atom);
		res.termVariables = supportset;
		atom.getAtom().setInstantiationVariables(supportset);
		return res;
	}

	FlatFormula convertDisjunction(FlatFormula lhs, FlatFormula rhs) {
		/* Check if lhs or rhs is equal to TRUE/FALSE */
		if (lhs.isTrue() || rhs.isTrue())
			return TRUE;
		if (lhs.isFalse())
			return rhs;
		if (rhs.isFalse())
			return lhs;
		Set<FlatFormula> disjunction = new HashSet<FlatFormula>();
		disjunction.addAll(lhs.getSubFormulas());
		disjunction.addAll(rhs.getSubFormulas());
		return createClauseFormula(disjunction);
	}

	/**
	 * Convert a smtlib formula to a single clause or negated clause by adding
	 * auxiliary literals and clauses fixing their values.
	 * 
	 * @param f
	 *            the formula to convert.
	 * @returns a clause representing formula f.
	 */
	private FlatFormula convertFormula(Formula f, int formNumber) {
		FlatFormula result = formulaCache.get(f);
		if (result != null)
			return result;
		if (f instanceof NegatedFormula) {
			result = convertFormula(((NegatedFormula) f).getSubFormula(), formNumber)
					.negate();
		} else if (f instanceof FletFormula) {
			Stack<FormulaVariable> fletStack = new Stack<FormulaVariable>();
			while (f instanceof FletFormula) {
				FletFormula flet = (FletFormula) f;
				FlatFormula flatform = convertFormula(flet.getValue(), formNumber);
				fletStack.push(flet.getVariable());
				fletTable.put(flet.getVariable(), flatform);
				f = flet.getSubFormula();
			}
			result = convertFormula(f, formNumber);
			while (!fletStack.isEmpty())
				fletTable.remove(fletStack.pop());
		} else if (f instanceof LetFormula) {
			LetFormula let = (LetFormula) f;
			FlatTerm tvalue = convertTerm(let.getValue(), formNumber);
			FlatTerm old = symbolicTerms.put(let.getVariable(), tvalue);
			result = convertFormula(let.getSubFormula(), formNumber);
			if (old == null)
				symbolicTerms.remove(let.getVariable());
			else
				symbolicTerms.put(let.getVariable(),old);
		} else if (f instanceof ConnectedFormula) {
			ConnectedFormula cf = (ConnectedFormula) f;
			int connector = cf.getConnector();
			FlatFormula lhs = convertFormula(cf.getLhs(), formNumber);
			if (connector == ConnectedFormula.IFF
					|| connector == ConnectedFormula.XOR) {
				/* Optimize repeated IFFs to prevent stack overflow. */
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula) cf.getRhs()).getConnector() == connector) {
					cf = (ConnectedFormula) cf.getRhs();
					FlatFormula llhs = convertFormula(cf.getLhs(), formNumber);
					lhs = createIfThenElse(lhs, llhs, llhs.negate());
					if (connector == ConnectedFormula.XOR)
						lhs = lhs.negate();
				}
				FlatFormula rhs = convertFormula(cf.getRhs(), formNumber);
				lhs = createIfThenElse(lhs, rhs, rhs.negate());
				if (connector == ConnectedFormula.XOR)
					lhs = lhs.negate();
				result = lhs;
			} else if (connector == ConnectedFormula.OR) {
				/* Optimize repeated disjunctions to prevent stack overflow. */
				Set<FlatFormula> disjunction = new HashSet<FlatFormula>();
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula) cf.getRhs()).getConnector() == connector) {
					if (lhs.isTrue())
						return TRUE;
					disjunction.addAll(lhs.getSubFormulas());
					cf = (ConnectedFormula) cf.getRhs();
					lhs = convertFormula(cf.getLhs(), formNumber);
				}
				if (lhs.isTrue())
					return TRUE;
				disjunction.addAll(lhs.getSubFormulas());
				FlatFormula rhs = convertFormula(cf.getRhs(), formNumber);
				if (rhs.isTrue())
					return TRUE;
				disjunction.addAll(rhs.getSubFormulas());
				result = createClauseFormula(disjunction);
			} else if (connector == ConnectedFormula.AND) {
				/* Optimize repeated conjunctions to prevent stack overflow. */
				Set<FlatFormula> disjunction = new HashSet<FlatFormula>();
				while (cf.getRhs() instanceof ConnectedFormula
						&& ((ConnectedFormula) cf.getRhs()).getConnector() == connector) {
					if (lhs.isFalse())
						return FALSE;
					disjunction.addAll(lhs.negate().getSubFormulas());
					cf = (ConnectedFormula) cf.getRhs();
					lhs = convertFormula(cf.getLhs(), formNumber);
				}
				if (lhs.isFalse())
					return FALSE;
				disjunction.addAll(lhs.negate().getSubFormulas());
				FlatFormula rhs = convertFormula(cf.getRhs(), formNumber);
				if (rhs.isFalse())
					return FALSE;
				disjunction.addAll(rhs.negate().getSubFormulas());
				result = createClauseFormula(disjunction).negate();
			} else {
				assert (connector == ConnectedFormula.IMPLIES);
				FlatFormula rhs = convertFormula(cf.getRhs(), formNumber);
				result = convertDisjunction(lhs.negate(), rhs);
			}
		} else if (f instanceof ITEFormula) {
			ITEFormula ite = (ITEFormula) f;
			FlatFormula cond = convertFormula(ite.getCondition(), formNumber);
			FlatFormula thenCase = convertFormula(ite.getTrueCase(), formNumber);
			FlatFormula elseCase = convertFormula(ite.getFalseCase(), formNumber);
			result = convertDisjunction(
					convertDisjunction(cond.negate(), thenCase).negate(),
					convertDisjunction(cond, elseCase).negate()).negate();
		} else if (f instanceof VariableAtom) {
			return fletTable.get(((VariableAtom) f).getVariable());
		} else if (f instanceof DistinctAtom) {
			Term[] terms = ((DistinctAtom) f).getTerms();
			Set<TermVariable> support = new HashSet<TermVariable>();
			FlatTerm[] diseqTerms = new FlatTerm[terms.length];
			for (int i = 0; i < diseqTerms.length; i++) {
				diseqTerms[i] = convertTerm(terms[i], formNumber);
				if (diseqTerms[i].termVariables != null)
					support.addAll(diseqTerms[i].termVariables);
			}
			Set<FlatFormula> equalities = new HashSet<FlatFormula>();
			for (int i = 0; i < diseqTerms.length; i++) {
				for (int j = i + 1; j < diseqTerms.length; j++) {
					if (diseqTerms[i] == diseqTerms[j]) {
						/* This distinct literal is not satisfiable */
						return FALSE;
					}
					FlatFormula eq = createEqualityFormula(diseqTerms[i],
							diseqTerms[j], formNumber);
					if (eq.isTrue())
						return FALSE;
					equalities.addAll(eq.getSubFormulas());
				}
			}
			result = createClauseFormula(equalities).negate();
			result.termVariables = support;
		} else if (f instanceof EqualsAtom) {
			Term[] terms = ((EqualsAtom) f).getTerms();
			FlatTerm[] eqTerms = new FlatTerm[terms.length];
			Set<TermVariable> support = new HashSet<TermVariable>();
			for (int i = 0; i < eqTerms.length; i++) {
				eqTerms[i] = convertTerm(terms[i], formNumber);
				if (eqTerms[i].termVariables != null)
					support.addAll(eqTerms[i].termVariables);
			}
			Set<FlatFormula> inequalities = new HashSet<FlatFormula>();
			for (int i = 0; i < eqTerms.length - 1; i++) {
				if (eqTerms[i] != eqTerms[i + 1]) {
					FlatFormula eq = createEqualityFormula(eqTerms[i],
							eqTerms[i + 1], formNumber);
					if (eq.isFalse())
						return FALSE;
					inequalities.addAll(eq.negate().getSubFormulas());
				}
			}
			result = createClauseFormula(inequalities).negate();
			result.termVariables = support;
		} else if (f instanceof PredicateAtom) {
			result = convertPredicate((PredicateAtom) f, formNumber);
		} else if (f == Atom.FALSE) {
			return FALSE;
		} else if (f == Atom.TRUE) {
			return TRUE;
		} else if (f instanceof QuantifiedFormula) {
			result = convertQuantifier((QuantifiedFormula) f, formNumber);
		} else {
			throw new IllegalArgumentException("Cannot handle formula " + f);
		}
		formulaCache.put(f, result);
		return result;
	}
	private Instantiation parentInst = null;

	/// Formula cache is only valid in this formula number!!!
	private int lastFormNumber = -1;
	private static int skolemcounter = 0;
	private final static Sort[] EMPTY_SORT_ARRAY = new Sort[0];
	private FlatFormula convertQuantifier(QuantifiedFormula f, int formNumber) {
		GroundMap.singletonGroundMap().addAuxEqs(this);
		Map<TermVariable,Term> skolem = GroundMap.singletonGroundMap().getSkolemization(f);
		Set<Instantiation> insts = GroundMap.singletonGroundMap().getInstantiations(f,parentInst);
		FlatFormula flatSkolem = null;
		if (skolem == null) {
			skolem = new HashMap<TermVariable, Term>(f.getVariables().length);
			for (TermVariable tv : f.getVariables()) {
				skolem.put(tv,dpllEngine.getSMTTheory().term(dpllEngine.getSMTTheory().createTempFunction(tv.getName()+"_CONVERTER_b"+skolemcounter++,EMPTY_SORT_ARRAY, tv.getSort())));
			}
		}
		Map<TermVariable,FlatTerm> oldmapping = new HashMap<TermVariable,FlatTerm>(skolem.size());
		for (Map.Entry<TermVariable, Term> me : skolem.entrySet()) {
			FlatTerm old = symbolicTerms.put(me.getKey(),convertTerm(me.getValue(),formNumber));
			if (old != null)
				oldmapping.put(me.getKey(),old);
		}
		flatSkolem = convertFormula(f.getSubformula(), formNumber);
		if (f.getQuantifier() == QuantifiedFormula.FORALL)
			flatSkolem = flatSkolem.negate();
		for (TermVariable tv : skolem.keySet())
			symbolicTerms.remove(tv);
		for (Map.Entry<TermVariable,FlatTerm> me : oldmapping.entrySet())
			symbolicTerms.put(me.getKey(),me.getValue());
		logger.debug(new DebugMessage("Converted skolem {0} with {1} to {2}.", f,skolem, flatSkolem));
		FlatFormula[] flatInsts = null;
		if (insts != null) {
			flatInsts = new FlatFormula[insts.size()];
			int dest = 0;
			Instantiation oldparent = parentInst;
			for (Instantiation inst : insts) {
				parentInst = inst;
				Map<TermVariable,Term> instmap = inst.getInstances();
				oldmapping.clear();
				for (Map.Entry<TermVariable, Term> me : instmap.entrySet()) {
					FlatTerm old = symbolicTerms.put(me.getKey(),convertTerm(me.getValue(),formNumber));
					if (old != null)
						oldmapping.put(me.getKey(),old);
				}
				flatInsts[dest] = convertFormula(f.getSubformula(), formNumber);
				if (f.getQuantifier() == QuantifiedFormula.EXISTS)
					flatInsts[dest] = flatInsts[dest].negate();
				++dest;
				for (TermVariable tv : instmap.keySet())
					symbolicTerms.remove(tv);
				for (Map.Entry<TermVariable,FlatTerm> me : oldmapping.entrySet())
					symbolicTerms.put(me.getKey(),me.getValue());
				logger.debug(new DebugMessage("Converted {0} with {1} to {2}.", f,inst, flatInsts[dest-1]));
			}// End of Instance iteration
			parentInst = oldparent;
		}
		Theory theory = dpllEngine.getSMTTheory();
		return f.getQuantifier() == QuantifiedFormula.FORALL ?
				new GroundifyForallFormula(this,f,flatInsts,flatSkolem) :
				new GroundifyForallFormula(this,
							theory.not(theory.exists(f.getVariables(),f.getSubformula(),f.getTriggers())),flatInsts,flatSkolem).negate();
//		throw new UnsupportedOperationException(
//				"Quantifiers are not supported by this Solver!");
		// TermVariable[] variables = f.getVariables();
		// int quant = f.getQuantifier();
		// CCTrigger[] triggers = new CCTrigger[f.getTriggers().length];
		// for (int i = 0; i < triggers.length; i++)
		// triggers[i] = CCTrigger.compile(f.getTriggers()[i]);
		// FlatFormula subform = convertFormula(f.getSubformula());
		// if (quant == QuantifiedFormula.FORALL)
		// return new ForallFormula(this, f, variables, triggers, subform);
		// else
		// return new ForallFormula(this, dpllEngine.getSMTTheory().not(f),
		// variables, triggers, subform.negate()).negate();
	}

	public ConvertFormula(DPLLEngine engine) {
		dpllEngine = engine;
		cclosure = new CClosure(dpllEngine);
		dpllEngine.addTheory(cclosure);
		logger = engine.getLogger();
	}

	public void addFormula(Formula f,int formNumber) {
		if (lastFormNumber  != formNumber) {
			formulaCache.clear();
			lastFormNumber = formNumber;
		}
		FlatFormula ff = convertFormula(f, formNumber);
		ff.addAsAxiom(formNumber);
		logger.info("Added " + numClauses + " clauses, " + numAtoms
				+ " auxiliary atoms.");
	}

	private int formulaCounter;
	public void addNOFormula(Formula f) {
		FlatFormula ff = convertFormula(f, formulaCounter-1);
		ff.addAsAxiom(formulaCounter-1);
	}

	public void addFormula(Formula f) {
		addFormula(f,formulaCounter);
		++formulaCounter;
		dpllEngine.incNumberOfFormulas();
	}

	public void close() {
		int numipls = formulaCounter - 1;
		Level oldLevel = logger.getLevel();
		logger.setLevel(Level.INFO);
		/* Normalize formula numbers of shared terms. */
		for (Map.Entry<AffinTerm,CCTerm> entry : linsumTerms.entrySet()) {
			AffinTerm lsum = entry.getKey();
			CCTerm cc = entry.getValue();
			if (!lsum.isConstant()) {
				cc.occursIn(lsum.getFirstFormulaNr());
				cc.occursIn(lsum.getLastFormulaNr());
			} else {
				cc.occursIn(0);
				cc.occursIn(formulaCounter - 1);
			}
			if (logger.isDebugEnabled())
				logger.debug("Shared NO term: "+lsum + " / " +cc);
		}
		
		Collection<AffinTerm> sharedTerms = new ArrayList<AffinTerm>(
				linsumTerms.keySet());
		Iterator<AffinTerm> it = sharedTerms.iterator();
		while (it.hasNext()) {
			AffinTerm lsum1 = it.next();
			it.remove();
			CCTerm cc1 = linsumTerms.get(lsum1);
			for (AffinTerm lsum2 : sharedTerms) {
				if (lsum2.isIntegral() != lsum1.isIntegral())
					continue;
				CCTerm cc2 = linsumTerms.get(lsum2);
				TermVariable mixedVar = null;
				int lfnr = Math.min(cc1.getLastFormula(), cc2.getLastFormula());
				int ffnr = Math.max(cc1.getFirstFormula(), cc2
						.getFirstFormula());
				if (ffnr > lfnr) {
					Theory t = dpllEngine.getSMTTheory();
					mixedVar = t.createFreshTermVariable("eqmix",
							cclosure.convertTermToSMT(cc1).getSort());
				}
				EqualityAtom eq = cclosure.createEquality(cc1, cc2, mixedVar);
				AffinTerm diff = lsum1.add(lsum2.negate());
				if (diff.isConstant()) {
					Literal lit = eq;
					if (!diff.equals(Rational.ZERO))
						lit = eq.negate();
					InterpolationInfo[] ipl = new InterpolationInfo[numipls];
					for (int i = 0; i < numipls; i++) {
						if (i < lfnr) {
							ipl[i] = InterpolationInfo.TRUE;
						} else {
							ipl[i] = InterpolationInfo.FALSE;
						}
					}
					dpllEngine.addClause(new Clause(new Literal[] { lit }, ipl));
				} else {
					LinArSolve solver = lsum1.isIntegral() ? intLinarSolver : linarSolver;
					Clause[] noclauses;
					if (cc1.getFirstFormula() > cc2.getFirstFormula())
						noclauses = solver.generateNelsonOppenClauses(lsum2, lsum1, eq, numipls);
					else
						noclauses = solver.generateNelsonOppenClauses(lsum1, lsum2, eq, numipls);

					for (Clause c : noclauses) {
						if (logger.isDebugEnabled())
							logger.debug("Adding NO clause: " + c);
						dpllEngine.addClause(c);
					}
				}
			}
		}
		logger.setLevel(oldLevel);
	}
	private boolean checkClauseSupportSet(Literal[] clause) {
		final HashSet<TermVariable> expsupport = new HashSet<TermVariable>();
		SymbolVisitor tvcollector = new SymbolVisitor(){
			HashSet<TermVariable> mask = new HashSet<TermVariable>();
			@Override
			public void done(Term input) {}
			@Override
			public void done(PredicateAtom pa) {}
			@Override
			public void endscope(TermVariable tv) {
				mask.remove(tv);
			}
			@Override
			public void endscopes(TermVariable[] tvs) {
				for (TermVariable tv : tvs)
					mask.remove(tv);
			}
			@Override
			public void let(TermVariable tv, Term mval) {
				mask.add(tv);
			}
			@Override
			public Formula predicate(PredicateAtom pa) {
				// Trigger argument descending
				return null;
			}
			@Override
			public void quantifier(TermVariable[] tvs) {
				for (TermVariable tv : tvs)
				mask.add(tv);
			}
			@Override
			public Term term(Term input) {
				if (input instanceof ApplicationTerm || input instanceof ITETerm)
					// Trigger argument descending
					return null;
				if (input instanceof VariableTerm) {
					TermVariable tv = ((VariableTerm)input).getVariable();
					if (!mask.contains(tv))
						expsupport.add(tv);
				}
				return input;
			}
			@Override
			public boolean unflet() {
				return false;
			}
			@Override
			public boolean unlet() {
				return false;
			}
		};
		FormulaWalker fw = new FormulaWalker(tvcollector,dpllEngine.getSMTTheory());
		for (Literal lit : clause) {
			if (lit.getAtom() instanceof NamedAtom) continue;
			Set<TermVariable> support = lit.getAtom().getInstantiationVariables();
			Formula smt = lit.getSMTFormula(dpllEngine.getSMTTheory());
			fw.process(smt);
			if (!expsupport.isEmpty()) {
				if (support == null) {
					logger.error("Support on " + lit + " is empty but should be " + expsupport);
					return false;
				}
				if (!support.equals(expsupport)) {
					logger.error("Support on " + lit + " differs! Is: " + support + " but should be: " + expsupport);
					return false;
				}
			}
			if (expsupport.isEmpty()) {
				if (!(support == null || support.isEmpty())) {
					logger.error("Expected empty support on " + lit + " but have " + support);
					return false;
				}
			}
			expsupport.clear();
		}
		return true;
	}

	public void addAuxEq(EqualsAtom eq, SymbolRange range) {
		// EqualsAtom only has two subterms here...
		// 0 is VariableTerm, 1 is the real instantiation
		Term[] args = eq.getTerms();
		int varidx;
		if (args[0] instanceof VariableTerm)
			varidx = 0;
		else
			varidx = 1;
		TermVariable tv = ((VariableTerm)args[varidx]).getVariable();
		// Add the equality to formula number "me.getValue().last"
		int subFormNr = range.last;
		FlatTerm tvterm = createFlat(cclosure.createTermVariableTerm(tv),args[varidx], subFormNr);
		tvterm.ccTerm.occursIn(range.last);
		FlatTerm instterm = convertTerm(args[1-varidx], subFormNr);
		FlatFormula flateq = createEqualityFormula(tvterm, instterm, subFormNr);
		flateq.addTermVariable(tv);
		if (instterm.termVariables != null)
			flateq.termVariables.addAll(instterm.termVariables);
		flateq.addAsAxiom(subFormNr);
	}
}
