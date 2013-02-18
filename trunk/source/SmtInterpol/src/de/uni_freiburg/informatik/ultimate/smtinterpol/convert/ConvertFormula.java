/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.QuantifiedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.QuantifierTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;
import de.uni_freiburg.informatik.ultimate.util.UnifyHash;

public class ConvertFormula {
	
	private Logger logger;
	ScopedHashMap<TermVariable, FlatTerm> letTable = new ScopedHashMap<TermVariable, FlatTerm>();

//	private final static SharedTermOld[] EMPTY_ARGS = {};
	Theory m_Theory;
	DPLLEngine dpllEngine;
	CClosure cclosure;
	LinArSolve linarSolver;
	QuantifierTheory quantTheory;
	ProofNode m_sourceAnnot, m_tautAnnot;
	InternalizerVisitor internalizer = new InternalizerVisitor();
	ContextOptimizer m_optimizer;
	ScopedHashMap<TermVariable, Term> m_auxVariables = new ScopedHashMap<TermVariable, Term>();
	int numClauses, numAtoms;
	// Set to true when we warn about pushing on an inconsistent benchmark.
	boolean warnedFailedPush = false;

	FlatFormula TRUE = new FlatFormula(this) {
		private Literal lit;
		public Literal getLiteral() {
			if (lit == null) {
				lit = m_converter.createAnonAtom(m_converter.getTheory().TRUE);
				m_converter.addClause(new Literal[] { lit });
				m_converter.m_RemoveLit.add(this);
			}
			return lit;
		}

		public FlatFormula negate() {
			return m_converter.FALSE;
		}

		public Term getSMTTerm(boolean useAuxVars) {
			return m_converter.getTheory().TRUE;
		}

		public void addAsAxiom(ClauseDeletionHook hook) {
			/* Nothing to do for TRUE */
		}

		public Set<FlatFormula> getSubFormulas() {
			throw new AssertionError("getSubFormulas() called on TRUE");
		}

		@Override
		public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
			sb.append("TRUE");
		}

		@Override
		public void literalRemoved() {
			lit = null;
		}

		public void accept(FlatTermVisitor visitor) {
			visitor.visitTrue(this);
		}
	};
	
	FlatFormula FALSE = new FlatFormula(this) {
		public Literal getLiteral() {
			return m_converter.TRUE.getLiteral().negate();
		}

		public FlatFormula negate() {
			return m_converter.TRUE;
		}

		public Term getSMTTerm(boolean useAuxVars) {
			return m_converter.getTheory().FALSE;
		}

		public void addAsAxiom(ClauseDeletionHook hook) {
			m_converter.addClause(new Literal[] {});
		}

		public Set<FlatFormula> getSubFormulas() {
			return Collections.emptySet();
		}

		@Override
		public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
			sb.append("FALSE");
		}

		public void accept(FlatTermVisitor visitor) {
			visitor.visitFalse(this);
		}
	};
	
	UnifyHash<ClauseFormula> clauseFFs =
		new UnifyHash<ClauseFormula>();
	UnifyHash<FlatTerm> unifiedTerms = new UnifyHash<FlatTerm>();
	ScopedHashMap<AffineTerm, EqualityFormula> m_equalities =
		new ScopedHashMap<AffineTerm, EqualityFormula>();
	
	ScopedArrayList<SharedTermOld> m_UnshareCC = new ScopedArrayList<SharedTermOld>();
	ScopedArrayList<SharedTermOld> m_UnshareLA = new ScopedArrayList<SharedTermOld>();
	ScopedArrayList<FlatFormula> m_RemoveLit =
		new ScopedArrayList<FlatFormula>();
	
	ScopedHashSet<BooleanVarAtom> m_BooleanVars = null;
	
	ScopedHashSet<Sort> m_arraySorts = new ScopedHashSet<Sort>();
//	StackedList<FlatTerm> m_arrayterms = new StackedList<FlatTerm>();
	
	IPatternCompiler patternCompiler = null;
	
	/**
	 * The stack level for push/pop commands.  This is the number of issued 
	 * push commands that have no corresponding pop commands.
	 */
	int m_stackLevel;
	
	// Count the number of pushs on an inconsistent solver.
	private int numfailedpush = 0;
	
	public void setupCClosure() {
		if (cclosure == null) {
//			cclosure = new CClosure(dpllEngine,this);
			dpllEngine.addTheory(cclosure);
			createEqualityFormula(TRUE, FALSE).negate().addAsAxiom(null);
		}
	}
	
	public void setupLinArithmetic() {
		if (linarSolver == null) {
			linarSolver = new LinArSolve(dpllEngine);
			dpllEngine.addTheory(linarSolver);
		}
	}
	
	public void setupQuantifiers() {
		setupCClosure();
		try {
			Class<?> pcclass = getClass().getClassLoader().loadClass(
					System.getProperty(
							Config.PATTERNCOMPILER,
							Config.DEFAULT_PATTERNCOMPILER));
			patternCompiler = (IPatternCompiler)pcclass.newInstance();
		} catch (Exception e) {
			logger.fatal("Could not load Pattern Compiler",e);
			throw new RuntimeException("Could not load Pattern Compiler",e);
		}
		quantTheory = new QuantifierTheory(cclosure);
		dpllEngine.addTheory(quantTheory);
	}
	
	public void setLogic(Logics logic) {
		switch (logic) {
		case CORE:
			break;
		case QF_UFLRA:
		case QF_UFLIRA:
		case QF_UFLIA:
		case QF_UFIDL:
			setupCClosure();
			setupLinArithmetic();
			break;
		case QF_IDL:
		case QF_LIA:
		case QF_LRA:
		case QF_RDL:
			setupLinArithmetic();
			break;
		case QF_UF:
			setupCClosure();
			break;
		default:
			throw new UnsupportedOperationException(
					"Logic " + logic.toString() + " unsupported");
		}
	}
	
	public void setSourceAnnotation(SourceAnnotation sourceAnnot) {
		m_sourceAnnot = new LeafNode(LeafNode.NO_THEORY, sourceAnnot);
		// This is broken, but should be unused!!!
		m_tautAnnot = new LeafNode(LeafNode.NO_THEORY, sourceAnnot);
	}
	
	public Theory getTheory() {
		return m_Theory;
	}

	FlatTerm createDivideTerm(AffineTerm dividend, Rational divisor) {
		int hash = dividend.hashCode()*17 + divisor.hashCode();
		for (FlatTerm t : unifiedTerms.iterateHashCode(hash)) {
			if (t instanceof DivideTerm) {
				DivideTerm divTerm = (DivideTerm) t;
				if (divTerm.m_affineTerm.equals(dividend)
						&& divTerm.m_divisor.equals(divisor)) {
//					divTerm.createAxioms();
					return divTerm;
				}
			}
		}
		DivideTerm divTerm = new DivideTerm(dividend, divisor);
//		divTerm.createAxioms();
		unifiedTerms.put(hash, divTerm);
		return divTerm;
	}

		
	FlatFormula createClauseFormula(Set<FlatFormula> subforms) {
		if (subforms.size() == 0)
			return FALSE;
		if (subforms.size() == 1)
			return subforms.iterator().next();
		int hash = subforms.hashCode();
		
		for (ClauseFormula cf : clauseFFs.iterateHashCode(hash)) {
			Collection<FlatFormula> subs = cf.getSubFormulas(); 			
			if (subforms.size() == subs.size()
				&& subforms.containsAll(subs)) {
				return cf;
			}
		}
		FlatFormula[] subformsArray = 
			subforms.toArray(new FlatFormula[subforms.size()]);
		ClauseFormula cf = new ClauseFormula(this, subformsArray);
		clauseFFs.put(hash, cf);
		return cf;
	}

	FlatFormula createIfThenElse(FlatFormula cond,
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


	public void addClause(Literal[] literals) {
		addClause(literals, null, false);
	}
	
	public void addClause(Literal[] literals, ClauseDeletionHook hook,
			boolean tautology) {
//		assert(checkClauseSupportSet(literals));
		/* simplify clause by merging identical literals */
		HashSet<Literal> lits = new HashSet<Literal>();
		lits.addAll(Arrays.asList(literals));
		if (lits.size() != literals.length)
			literals = lits.toArray(new Literal[lits.size()]);
		
		/* check for trivial tautologies */
		for (Literal l : literals)
			if (lits.contains(l.negate()))
				return;
		
		dpllEngine.addFormulaClause(literals,
				tautology ? m_tautAnnot : m_sourceAnnot, hook);
		numClauses++;
		if (logger.isDebugEnabled())
			logger.debug("Adding clause: " + lits);
	}
	
	/**
	 * Add a clause that might be removed during the search to the engine.
	 * @param literals	Clause literals.
	 * @param hook		Hook to call once the clause gets removed.
	 */
	public void learnClause(Literal[] literals, ClauseDeletionHook hook) {
		/* simplify clause by merging identical literals */
		HashSet<Literal> lits = new HashSet<Literal>();
		lits.addAll(Arrays.asList(literals));
		if (lits.size() != literals.length)
			literals = lits.toArray(new Literal[lits.size()]);
		
		/* check for trivial tautologies */
		for (Literal l : literals)
			if (lits.contains(l.negate()))
				return;
		
		Clause clause = new Clause(literals);
		clause.setDeletionHook(hook);
		dpllEngine.learnClause(clause);
		numClauses++;
		if (logger.isDebugEnabled())
			logger.debug("Learning additional clause: " + lits);
	}
	
	TermVariable createAuxVariable(Term smtTerm) {
		TermVariable name = m_Theory.createFreshTermVariable("aux", smtTerm.getSort());
		m_auxVariables.put(name, smtTerm);
		return name;
	}

	NamedAtom createAnonAtom(Term smtFormula) {
		NamedAtom atom = new NamedAtom(smtFormula, m_stackLevel);
		dpllEngine.addAtom(atom);
		numAtoms++;
		return atom;
	}

	BooleanVarAtom createBooleanVar(Term smtFormula) {
		BooleanVarAtom atom = new BooleanVarAtom(smtFormula, m_stackLevel);
		if (m_BooleanVars != null)
			m_BooleanVars.add(atom);
		dpllEngine.addAtom(atom);
		numAtoms++;
		return atom;
	}

	QuantifiedAtom createQuantifiedAtom(Term smtFormula) {
		String name = "quantproxy!" + numAtoms;
		QuantifiedAtom atom = new QuantifiedAtom(name, smtFormula, m_stackLevel);
		dpllEngine.addAtom(atom);
		++numAtoms;
		return atom;
	}
	
	FlatTerm createApplicationTerm(FunctionSymbol sym, FlatTerm[] flatArgs)
	{
		SharedTermOld[] args = new SharedTermOld[flatArgs.length];
		for (int i = 0 ; i < args.length; i++)
			args[i] = flatArgs[i].toShared();
		int hash = sym.hashCode() ^ Arrays.hashCode(args);
		for (FlatTerm term : unifiedTerms.iterateHashCode(hash)) {
			if (term instanceof FlatApplicationTerm) {
				FlatApplicationTerm appTerm = (FlatApplicationTerm) term;
				if (appTerm.m_Symbol.equals(sym)
					&& Arrays.equals(appTerm.m_Parameters, args)) {
					// Force creation of ccterm to implement congruence.
//					if (args.length != 0)
//						appTerm.toCCTerm();
					return appTerm;
				}
			}
		}
		FlatApplicationTerm appTerm = new FlatApplicationTerm(this, sym, args);
		unifiedTerms.put(hash, appTerm);
		// Force creation of ccterm to implement congruence.
//		if (args.length != 0)
//			appTerm.toCCTerm();
		return appTerm;
	}
	
	public SharedTermOld createSharedAffineTerm(AffineTerm at) {
		int hash = at.hashCode();
		for (FlatTerm term : unifiedTerms.iterateHashCode(hash)) {
			if (term instanceof SharedAffineTerm) {
				SharedAffineTerm shared = (SharedAffineTerm) term;
				// shared.getOffset() == null means shared is deleted by pop
				if (shared.m_affineTerm.equals(at)/* && shared.getOffset() != null*/) {
//					shared.shareWithLinAr();
					return shared;
				}
			}
		}
		SharedAffineTerm shared = new SharedAffineTerm(this, at);
//		shared.shareWithLinAr();
		unifiedTerms.put(hash, shared);
		return shared;
	}
	
	public FlatFormula createBooleanVariable(FunctionSymbol pred) {
		Term atom = m_Theory.term(pred);
		int hash = pred.hashCode();
		for (FlatTerm term : unifiedTerms.iterateHashCode(hash)) {
			if (term instanceof LiteralFormula) {
				LiteralFormula form = (LiteralFormula) term;
				if (form.getSMTTerm() == atom) {
					return form;
				}
			}
		}
		LiteralFormula form = new LiteralFormula(this, atom);
		unifiedTerms.put(hash, form);
		return form;
	}

	private FlatTerm convertFuncTerm(FunctionSymbol func, FlatTerm[] args) {
//		if (func.getReturnSort().getName().equals("Array")) {
//			createArrayAxioms(func.getReturnSort());
//		}
		if (m_Theory.getLogic().isIRA() && func.getParameterCount() == 2 && 
			func.getParameterSort(0).getName().equals("Real") && 
			func.getParameterSort(1).getName().equals("Real")) {
			// IRA-Hack
			for (int i = 0; i < args.length; i++) {
				if (args[i].getSort().getName().equals("Int"))
					args[i] = new AffineTerm(args[i].toAffineTerm(), func.getParameterSort(0));
			}
		}
		
		Term definition = func.getDefinition();
		if (definition != null) {
			letTable.beginScope();
			TermVariable[] vars = func.getDefinitionVars();
			for (int i = 0; i < vars.length; i++)
				letTable.put(vars[i], args[i]);
			FlatTerm result = convertTerm(definition);
			letTable.endScope();
			return result;
		}
		if (func.isIntern()) {
			if (func.getName().equals("+") && func.getParameterCount() == 2) {
				return args[0].toAffineTerm().add(args[1].toAffineTerm());
			}
			else if (func.getName().equals("-") && func.getParameterCount() == 2) {
				return args[0].toAffineTerm().add(args[1].toAffineTerm().negate());
			} 
			else if (func.getName().equals("*") && func.getParameterCount() == 2) {
				AffineTerm arg0 = args[0].toAffineTerm();
				AffineTerm arg1 = args[1].toAffineTerm();
				if (arg0.isConstant()) {
					return new AffineTerm(arg0.getConstant(), arg1);
				} else if (arg1.isConstant()) {
					return new AffineTerm(arg1.getConstant(), arg0);
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (func.getName().equals("/") && func.getParameterCount() == 2) {
				AffineTerm arg0 = args[0].toAffineTerm();
				AffineTerm arg1 = args[1].toAffineTerm();
				if (arg1.isConstant()) {
					return new AffineTerm(arg1.getConstant().inverse(), arg0);
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (func.getName().equals("div") && func.getParameterCount() == 2) {
				AffineTerm arg0 = args[0].toAffineTerm();
				AffineTerm arg1 = args[1].toAffineTerm();
				if (arg1.isConstant()) {
					return createDivideTerm(arg0, arg1.getConstant());
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (func.getName().equals("mod") && func.getParameterCount() == 2) {
				AffineTerm arg0 = args[0].toAffineTerm();
				AffineTerm arg1 = args[1].toAffineTerm();
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral() && 
				    !divisor.equals(Rational.ZERO)) {
					FlatTerm divTerm = createDivideTerm(arg0, arg1.getConstant());
					return arg0.add(new AffineTerm(arg1.getConstant().negate(),
												   divTerm.toAffineTerm()));
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (func.getName().equals("-") && func.getParameterCount() == 1) {
				return args[0].toAffineTerm().negate();
			} else if (func.getName().equals("abs") && func.getParameterCount() == 1) {
				AffineTerm arg = args[0].toAffineTerm();
				AffineTerm argNeg = arg.negate();
				return createIteTerm(createLeq0Formula(argNeg), 
									 arg.toShared(), argNeg.toShared());
			} else if (func.getName().equals("to_real") && func.getParameterCount() == 1) {
				return new AffineTerm(args[0].toAffineTerm(), func.getReturnSort());
			} else if (func.getName().equals("to_int") && func.getParameterCount() == 1) {
				return createDivideTerm(args[0].toAffineTerm(), Rational.ONE);
//			} else if (func.getName().equals("store")) {
//				return createApplicationTerm(func, args);
//			} else if (func.getName().equals("select")) {
//				if (args[1].getSort().getName().equals("Array"))
//					cclosure.addForeignArray(args[1].toCCTerm());
//				return createApplicationTerm(func, args);
			} else {
				throw new UnsupportedOperationException
					("Internal function "+func+" is not yet supported.");
			}
		}
//		for (FlatTerm arg : args) {
//			if (arg.getSort().getName().equals("Array"))
//				cclosure.addForeignArray(arg.toCCTerm());
//		}
		return createApplicationTerm(func, args);
	}

	FlatTerm createIteTerm(FlatFormula cond, 
			SharedTermOld trueCase, SharedTermOld falseCase) {
		if (cond.isTrue())
			return trueCase;
		if (cond.isFalse())
			return falseCase;
		if (trueCase == falseCase)
			return trueCase;
		int hash = (cond.hashCode()*17 + trueCase.hashCode()) * 17
			+ falseCase.hashCode();
		for (FlatTerm term : unifiedTerms.iterateHashCode(hash)) {
			if (term instanceof IfThenElseTerm) {
				IfThenElseTerm iteTerm = (IfThenElseTerm) term;
				if (iteTerm.mCond == cond
						&& iteTerm.mThen == trueCase
						&& iteTerm.mElse == falseCase)
					return iteTerm;
			}
		}
		IfThenElseTerm iteTerm =
			new IfThenElseTerm(this, cond, trueCase, falseCase);
		unifiedTerms.put(hash, iteTerm);
		return iteTerm;
	}

	FlatFormula createLeq0Formula(AffineTerm linsum) {
		if (linsum.isConstant()) {
			return linsum.getConstant().compareTo(Rational.ZERO) <= 0 ? TRUE
					: FALSE;
		}
		linsum = linsum.div(linsum.getGcd().abs());
		int hash = linsum.hashCode() * 17 + 1;
		for (FlatTerm term : unifiedTerms.iterateHashCode(hash)) {
			if (term instanceof LeqZeroFormula) {
				LeqZeroFormula form = (LeqZeroFormula) term;
				if (form.mTerm.equals(linsum))
					return form;
			}
		}
		LeqZeroFormula form = new LeqZeroFormula(this, linsum);
		unifiedTerms.put(hash, form);
		return form;
	}
	
	FlatFormula createEqualityFormula(FlatTerm t1, FlatTerm t2) {
		AffineTerm diff = t1.toAffineTerm().add(t2.toAffineTerm().negate());
		if (diff.isConstant())
			return diff.getConstant().equals(Rational.ZERO) ? TRUE : FALSE;
		diff = diff.div(diff.getGcd());
		// check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (diff.isIntegral() && !diff.getConstant().isIntegral())
			return FALSE;
		// we cannot really normalize the sign of the term.  Try both signs.
		EqualityFormula eqForm = m_equalities.get(diff);
		if (eqForm != null)
			return eqForm;
		eqForm = m_equalities.get(diff.negate());
		if (eqForm != null)
			return eqForm;
		eqForm = new EqualityFormula(this, t1.toShared(), t2.toShared());
		m_equalities.put(diff, eqForm);
		return eqForm;
	}
	
	public Literal getEqualityLiteral(FlatTerm f1, FlatTerm f2) {
		return createEqualityFormula(f1, f2).getLiteral();
	}
	
	private FlatFormula convertPredicate(FunctionSymbol pred, FlatTerm[] args) {
		FlatFormula result;
		if (m_Theory.getLogic().isIRA() && pred.getParameterCount() == 2 && 
			pred.getParameterSort(0).getName().equals("Real") && 
			pred.getParameterSort(1).getName().equals("Real")) {
			// IRA-Hack
			for (int i = 0; i < args.length; i++) {
				if (args[i].getSort().getName().equals("Int"))
					args[i] = new AffineTerm(args[i].toAffineTerm(), pred.getParameterSort(0));
			}
		}
		Term definition = pred.getDefinition();
		if (definition != null) {
			letTable.beginScope();
			TermVariable[] vars = pred.getDefinitionVars();
			for (int i = 0; i < vars.length; i++)
				letTable.put(vars[i], args[i]);
			result = convertFormula(definition);
			letTable.endScope();
			return result;
		}
		if (pred.isIntern()) {
			if (args.length == 2 && pred.getName().equals("=")) {
				if (args[0].getSort() == getTheory().getBooleanSort()) 
					return createIfThenElse((FlatFormula) args[0], (FlatFormula) args[1], ((FlatFormula) args[1]).negate());
				return createEqualityFormula(args[0], args[1]);
			} else if (args.length == 2 && pred.getName().equals("distinct")) {
				if (args[0].getSort() == getTheory().getBooleanSort()) 
					return createIfThenElse((FlatFormula) args[0], (FlatFormula) args[1], ((FlatFormula) args[1]).negate()).negate();
				return createEqualityFormula(args[0], args[1]).negate();
			} else if (args.length == 2) {
				AffineTerm sum = args[0].toAffineTerm().
					add(args[1].toAffineTerm().negate());
				if (pred.getName().equals(">"))
					return createLeq0Formula(sum).negate();
				else if (pred.getName().equals("<"))
					return createLeq0Formula(sum.negate()).negate();
				else if (pred.getName().equals(">="))
					return createLeq0Formula(sum.negate());
				else if (pred.getName().equals("<="))
					return createLeq0Formula(sum);
			} else if (pred.getName().equals("is_int")) {
				FlatTerm intArg = 
					createDivideTerm(args[0].toAffineTerm(), Rational.ONE);
				return createEqualityFormula
					(args[0], new AffineTerm(intArg.toAffineTerm(), 
										     pred.getParameterSort(0)));
			} else if (pred.getName().equals("divisible")) {
				Rational divisor = Rational.valueOf(pred.getIndices()[0], BigInteger.ONE); 
				FlatTerm intArg = 
					createDivideTerm(args[0].toAffineTerm(), divisor);
				return createEqualityFormula
					(args[0], intArg.toAffineTerm().mul(divisor)); 
			}
			throw new UnsupportedOperationException
				("Internal predicate "+pred+" is not supported.");
		}
		if (args.length == 0)
			return createBooleanVariable(pred);
		if (cclosure == null) {
			throw new UnsupportedOperationException
				("Need UF to support predicates with arguments" + pred);
		}
		assert(pred.getDefinition() == null && !pred.isIntern());
		FlatTerm predicate = createApplicationTerm(pred, args);
		result = createEqualityFormula(predicate, TRUE);
		return result;
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
	 * Convert an smtlib formula to a flat formula.
	 * 
	 * @param term
	 *            the formula to convert.
	 * @returns a clause representing formula f.
	 */
	public FlatFormula convertFormula(Term term) {
		assert (term.getSort() == getTheory().getBooleanSort()) :
			"convertFormula called with non-boolean term "+term;
		if (term instanceof LetTerm) {
			letTable.beginScope();
			/* avoid recursion on let terms */
			while (term instanceof LetTerm) {
				LetTerm let = (LetTerm) term;
				Term[] values = let.getValues();
				FlatTerm[] tvalues = new FlatTerm[values.length];
				for (int i = 0; i < values.length; i++) {
					tvalues[i] = convertTerm(let.getValues()[i]);
				}
				for (int i = 0; i < values.length; i++) {
					letTable.put(let.getVariables()[i], tvalues[i]);
				}
				term = let.getSubTerm();
			}
			FlatFormula result = convertFormula(term);
			letTable.endScope();
			return result;
		}

		if (term instanceof ApplicationTerm) {
			if (term == m_Theory.TRUE)
				return TRUE;
			if (term == m_Theory.FALSE)
				return FALSE;
			ApplicationTerm appterm = (ApplicationTerm) term; 
			FunctionSymbol func = appterm.getFunction();
			Term[] params = appterm.getParameters();
			if (func == m_Theory.m_Not) {
				return convertFormula(params[0]).negate();
			} else if (func == m_Theory.m_And ||
					func == m_Theory.m_Or ||
					func == m_Theory.m_Implies) {
				Set<FlatFormula> disjunction = new HashSet<FlatFormula>();
				for (int i = 0; i < params.length; i++) {
					FlatFormula flat = convertFormula(params[i]);
					if (func == m_Theory.m_And
						|| (func == m_Theory.m_Implies && i < params.length-1))
						flat = flat.negate();
					if (flat.isTrue())
						return func == m_Theory.m_And ? FALSE : TRUE;
					disjunction.addAll(flat.getSubFormulas());
				}
				FlatFormula disjflat = createClauseFormula(disjunction);
				return func == m_Theory.m_And ? disjflat.negate() : disjflat;
			} else if (func == m_Theory.m_Xor) {
				FlatFormula result = FALSE;
				for (int i = 0; i < params.length; i++) {
					FlatFormula other = convertFormula(params[i]);
					result = createIfThenElse(result, other.negate(), other);
				}
				return result;
			} else if (func.isIntern() && func.getName().equals("ite")) {
				FlatFormula cond = convertFormula(params[0]);
				FlatFormula thenCase = convertFormula(params[1]);
				FlatFormula elseCase = convertFormula(params[2]);
				return createIfThenElse(cond, thenCase, elseCase);
			} else {
				FlatTerm[] flatTerms = new FlatTerm[params.length];
				for (int i = 0; i < params.length; i++)
					flatTerms[i] = convertTerm(params[i]);
				if (func.isChainable()) {
					Set<FlatFormula> disjunctions = new HashSet<FlatFormula>();
					for (int i = 0; i < params.length-1; i++) {
						FlatFormula pred = convertPredicate(func, 
								new FlatTerm[] { flatTerms[i], flatTerms[i+1] });
						if (pred.isFalse())
							return FALSE;
						disjunctions.addAll(pred.negate().getSubFormulas());
					}
					return createClauseFormula(disjunctions).negate();
				} else if (func.isPairwise()) {
					Set<FlatFormula> disjunctions = new HashSet<FlatFormula>();
					for (int i = 0; i < params.length; i++) {
						for (int j = i + 1; j < params.length; j++) {
							FlatTerm[] pair = 
								new FlatTerm[] { flatTerms[i], flatTerms[j] };
							FlatFormula atom = 
								convertPredicate(func, pair);
							if (atom.isFalse())
								return FALSE;
							disjunctions.addAll(atom.negate().getSubFormulas());
						}
					}
					return createClauseFormula(disjunctions).negate();
				} else {
					return convertPredicate(func, flatTerms);
				}
			}
		} else if (term instanceof TermVariable) {
			FlatFormula result = (FlatFormula) 
				letTable.get((TermVariable) term);
			if (result == null) {
				throw new IllegalArgumentException("Variable " + term
						+ " undeclared");
			}
			return result;
		} else if (term instanceof AnnotatedTerm) {
			FlatFormula ff = convertFormula(((AnnotatedTerm)term).getSubterm());
			if (dpllEngine.isProduceAssignments()) {
				AnnotatedTerm at = (AnnotatedTerm)term;
				Annotation[] annots = at.getAnnotations();
				for (Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						dpllEngine.trackAssignment(a.getValue().toString(),
								ff.getLiteral());
						// HACK: We need a Tseitin-Encoding for these terms.
						//       Plaisted--Greenbaum is not enough!
						ff.negate().getLiteral();
					}
				}
			}
			return ff;
		} else if (term instanceof QuantifiedFormula) {
			return convertQuantifier((QuantifiedFormula) term);
		} else {
			throw new IllegalArgumentException("Cannot handle formula " + term);
		}
	}
	public FlatTerm convertTerm(Term term) {
		FlatTerm res;
		if (term.getSort() == m_Theory.getBooleanSort()) {
			res = convertFormula(term);
		} else if (term instanceof LetTerm) {
			letTable.beginScope();
			/* avoid recursion on let terms */
			while (term instanceof LetTerm) {
				LetTerm let = (LetTerm) term;
				TermVariable[] vars = let.getVariables();
				Term[] values = let.getValues();
				FlatTerm[] tvalues = new FlatTerm[values.length];
				for (int i = 0; i < values.length; i++) {
					tvalues[i] = convertTerm(values[i]);
				}
				for (int i = 0; i < values.length; i++) {
					letTable.put(vars[i], tvalues[i]);
				}
				term = let.getSubTerm();
			}
			res = convertTerm(term);
			letTable.endScope();
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appterm = (ApplicationTerm) term; 
			FunctionSymbol func = appterm.getFunction();
			FlatTerm[] args = new FlatTerm[appterm.getParameters().length];
			for (int i = 0; i < args.length; i++)
				args[i] = convertTerm(appterm.getParameters()[i]);
			if (func.isIntern() && func.getName().equals("ite")) {
				res = createIteTerm
					((FlatFormula) args[0], args[1].toShared(), args[2].toShared()); 
			} else if (func.isRightAssoc()) {
				FlatTerm result = args[args.length-1];
				for (int i = args.length-2; i >= 0; i++) {
					result = convertFuncTerm
						(func, new FlatTerm[] { args[i], result });
				}
				res = result;
			} else if (func.isLeftAssoc()) {
				FlatTerm result = args[0];
				for (int i = 1; i < args.length; i++) {
					result = convertFuncTerm
						(func, new FlatTerm[] { result, args[i] });
				}
				res = result;
			} else {
				res = convertFuncTerm(func, args);
			}
		} else if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			res = letTable.get(tv);
			if (res == null) {
				throw new IllegalArgumentException("Variable " + term
						+ " undeclared");
			}
		} else if (term instanceof ConstantTerm) {
			ConstantTerm numterm = (ConstantTerm) term;
			Object value = numterm.getValue();
			if (value instanceof BigInteger) {
				Rational rat = Rational.valueOf((BigInteger) value, BigInteger.ONE);
				res = new AffineTerm(this, rat, term.getSort());
			} else if (value instanceof BigDecimal) {
				BigDecimal decimal = (BigDecimal) value;
				Rational rat;
				if (decimal.scale() <= 0) {
					BigInteger num = decimal.toBigInteger();
					rat = Rational.valueOf(num, BigInteger.ONE);
				} else {
					BigInteger num = decimal.unscaledValue();
					BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					rat = Rational.valueOf(num, denom);
				}
				res = new AffineTerm(this, rat, term.getSort());
			} else if (value instanceof Rational) {
				res = new AffineTerm(this, (Rational) value, term.getSort());
			} else {
				/* string constant? */
				throw new UnsupportedOperationException
					("unsupported constant term "+term); 
			}
		} else if (term instanceof AnnotatedTerm) {
			/* ignore annotation for now */
			// XXX Should we also unify this kind of terms?
			return convertTerm(((AnnotatedTerm)term).getSubterm());
		} else {
			throw new IllegalArgumentException("Cannot handle: " + term);
		}
		return res;
	}

	private FlatFormula convertQuantifier(QuantifiedFormula f) {
		// TODO: Optimize sub, DER...
		Set<TermVariable> infervars = 
			eliminateUnusedVariables(f.getSubformula(), f.getVariables());
		if (infervars.isEmpty())
			return convertFormula(f.getSubformula());
		Term[][] trigs = 
			extractGivenPatterns(infervars, f.getSubformula());
		if (trigs == null) {
			trigs = inferTriggerFor(f.getSubformula(), infervars);
		}
		if (trigs == null) {
			logger.warn("Did not find pattern for quantified formula " + f);
		}
		FlatFormula res = new ForallFormula(this,f,infervars,trigs,
				f.getSubformula());
		return f.getQuantifier() == QuantifiedFormula.EXISTS ? res.negate() : res;
	}
	
	/**
	 * Return the conversion of a let bound variable.
	 * @param letVar Let-Bound variable.
	 * @return Conversion of this variable.
	 */
	public FlatTerm getTermForLetVar(TermVariable letVar) {
		return letTable.get(letVar);
	}
	
	private Term[][] extractGivenPatterns(Set<TermVariable> vars,Term sub) {
		List<Term[]> patterns = new ArrayList<Term[]>();
		while (sub instanceof AnnotatedTerm) {
			AnnotatedTerm at = (AnnotatedTerm)sub;
			Annotation[] annots = at.getAnnotations();
			for (Annotation a : annots) {
				if (a.getKey().equals(":pattern"))
					patterns.add((Term[])a.getValue());
			}
			sub = at.getSubterm();
		}
		if (!patterns.isEmpty()) {
//			TriggerData[] trigs = new TriggerData[patterns.size()];
//			int i = 0;
//			for (Term[] trig : patterns) {
//				trigs[i] = patternCompiler.compile(vars,trig,this);
//				trigs[i].yieldTrigger.postInit(this, letTable, sub, iu);
//				++i;
//			}
//			return trigs;
			return patterns.toArray(new Term[patterns.size()][]);
		}
		return null;
	}

	private Set<TermVariable> eliminateUnusedVariables(Term sub,
			TermVariable[] vars) {
		Set<TermVariable> freevars = new HashSet<TermVariable>(
				Arrays.asList(sub.getFreeVars()));
		Set<TermVariable> infervars = new HashSet<TermVariable>();
		if (!freevars.isEmpty()) {
			for (TermVariable tv : vars) {
				if (!freevars.contains(tv)) {
					if (Config.DEBUG_QVAR_ELIMINATION)
						logger.debug("Eliminating unused variable: " + tv);
				} else
					infervars.add(tv);
			}
		}
		return infervars;
	}
	
	private Term[][] inferTriggerFor(Term sub,	Set<TermVariable> vars) {
		assert(!vars.isEmpty());
		TriggerCandidateMap tcm = 
			new TriggerCandidateMap(dpllEngine.getLogger(),m_Theory,vars);
		tcm.insert(sub);
		Term[] trigs = tcm.getAllUnitTriggers();
		if (trigs != null) {
//			TriggerData[] tds = new TriggerData[trigs.length];
//			Term[] unittrig = new Term[1];
//			for (int i = 0; i < tds.length; ++i) {
//				unittrig[0] = trigs[i];
//				tds[i] = patternCompiler.compile(vars,unittrig,this);
//				tds[i].yieldTrigger.postInit(this, letTable, sub, iu);
//			}
//			return tds;
			Term[][] res = new Term[trigs.length][];
			for (int i = 0; i < trigs.length; ++i)
				res[i] = new Term[] {trigs[i]};
			return res;
		}
		trigs = tcm.getMultiTrigger();
		if (trigs != null) {
//			TriggerData[] res = new TriggerData[] {
//				patternCompiler.compile(vars,trigs,this)
//			};
//			res[0].yieldTrigger.postInit(this, letTable, sub, iu);
//			return res;
			return new Term[][]{trigs};
		}
		return null;
	}
	
	public ConvertFormula(DPLLEngine engine) {
		dpllEngine = engine;
		logger = engine.getLogger();
		m_Theory = engine.getSMTTheory();
		m_optimizer = new ContextOptimizer(this);
	}

	public void addFormula(Term f) {
		if (dpllEngine.inconsistent()) {
			logger.warn("Already inconsistent.");
			return;
		}
		if (dpllEngine.isProofGenerationEnabled()) {
			setSourceAnnotation(
					new SourceAnnotation("", f));
			if (f instanceof AnnotatedTerm) {
				AnnotatedTerm at = (AnnotatedTerm)f;
				Annotation[] annots = at.getAnnotations();
				for (Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						String name = ((String) a.getValue()).intern();
						setSourceAnnotation(new SourceAnnotation(name,
								at.getSubterm()));
						break;
					}
				}
			}
		}
		FlatFormula ff = convertFormula(f);
		if (logger.isDebugEnabled()) {
			logger.debug("Converted "+f);
			logger.debug(" into "+ff);
		}
		if (Config.OPTIMIZE_ALWAYS) {
			m_optimizer.reset();
			ff = (FlatFormula)m_optimizer.transform(ff);
			if (logger.isDebugEnabled())
				logger.debug("Optimized into " + ff);
		}
		ff.accept(internalizer);
		ff.addAsAxiom(null);
		internalizer.reset();
		logger.info("Added " + numClauses + " clauses, " + numAtoms
				+ " auxiliary atoms.");
		if (dpllEngine.isProofGenerationEnabled())
			setSourceAnnotation(null);
	}
	
	public void push() {
		if (dpllEngine.inconsistent()) {
			if (!warnedFailedPush) {
				logger.warn("Already inconsistent.");
				warnedFailedPush = true;
			}
			++numfailedpush;
		} else {
			dpllEngine.push();
			++m_stackLevel;
			m_auxVariables.beginScope();
			m_equalities.beginScope();
			m_arraySorts.beginScope();
			m_RemoveLit.beginScope();
			m_UnshareCC.beginScope();
			m_UnshareLA.beginScope();
			if (m_BooleanVars != null)
				m_BooleanVars.beginScope();
		}
	}
	public void pop(int numpops) {
		if (numpops <= numfailedpush) {
			numfailedpush -= numpops;
			return;
		}
		warnedFailedPush = false; 
		numpops -= numfailedpush;
		numfailedpush = 0;
		dpllEngine.pop(numpops);
		for (int i = 0; i < numpops; ++i) {
			if (m_BooleanVars != null)
				m_BooleanVars.endScope();
			m_arraySorts.endScope();
			for (SharedTermOld t : m_UnshareCC.currentScope())
				t.unshareCC();
			m_UnshareCC.endScope();
			for (SharedTermOld t : m_UnshareLA.currentScope())
				t.unshareLA();
			m_UnshareLA.endScope();
			for (FlatFormula f : m_RemoveLit.currentScope())
				f.literalRemoved();
			m_RemoveLit.endScope();
			m_equalities.endScope();
			m_auxVariables.endScope();
			m_stackLevel--;
		}
	}

	public CClosure getCClosure() {
		return cclosure;
	}
//	public FlatTerm createSkolemConstantFor(TermVariable tv) {
//		return new FlatApplicationTerm(this,
//				m_Theory.skolemize(tv, quantTheory.skolemcounter()),EMPTY_ARGS);
//	}
	
//	private void createArrayAxioms(Sort s) {
//		if (!m_arraySorts.contains(s)) {
//			m_arraySorts.add(s);
//			if (logger.isDebugEnabled())
//				logger.debug("Creating array axioms for sort " + s);
//			Sort indexSort = s.getArguments()[0];
//			Sort contentSort = s.getArguments()[1];
//			FunctionSymbol select = 
//				m_Theory.getFunction("select", s,indexSort);
//			FunctionSymbol store =
//				m_Theory.getFunction("store", s,indexSort,contentSort);
//			TermVariable arr = m_Theory.createTermVariable("a", s);
//			TermVariable index1 = m_Theory.createTermVariable("i", indexSort);
//			TermVariable index2 = m_Theory.createTermVariable("j", indexSort);
//			TermVariable elem = m_Theory.createTermVariable("e", contentSort);
//			Term selstore1 = m_Theory.term(select,
//					m_Theory.term(store,arr,index1,elem),index1);
//			Term selstore2 = m_Theory.term(select,
//					m_Theory.term(store,arr,index1,elem),index2);
//			Term sub1 = m_Theory.equals(selstore1,elem);
//			Term sub2 = m_Theory.implies(
//					m_Theory.distinct(index1,index2),
//					m_Theory.equals(selstore2,m_Theory.term(select,arr,index2)));
//			quantTheory.createArrayAxioms(this,sub1,sub2,select,store,arr,
//					index1,index2,elem);
//		}
//	}
//	
//	public Literal createExtensionalityDiseq(FlatTerm t1,FlatTerm t2) {
//		FlatTerm sk = createSkolemConstantFor(
//				m_Theory.createTermVariable("arrayex",
//						t1.getSort().getArguments()[0]));
//		if (logger.isDebugEnabled()) {
//			logger.debug("Adding Extensionality diseq for " + t1 + " ~ " + t2 + " using " + sk);
//		}
//		FunctionSymbol select = m_Theory.getFunction("select",
//				t1.getSort(),t1.getSort().getArguments()[0]);
//		FlatTerm[] args1 = { t1, sk };
//		FlatTerm[] args2 = { t2, sk };
//		FlatTerm lhs = createApplicationTerm(select,args1);
//		FlatTerm rhs = createApplicationTerm(select, args2);
//		return createEqualityFormula(lhs, rhs).negate().getLiteral();
//	}
//	public void addExtensionalityDiseqClause(FlatTerm t1,FlatTerm t2) {
//		Literal l1 = createEqualityFormula(t1, t2).getLiteral();
//		Literal l2 = createExtensionalityDiseq(t1, t2);
//		addClause(new Literal[] {l1,l2});
//	}

	public Logger getLogger() {
		return logger;
	}

	public DPLLEngine getEngine() {
		return dpllEngine;
	}

	public Term simplify(Term term) {
		FlatTerm ft = convertTerm(term);
		if (ft instanceof FlatFormula) {
			m_optimizer.reset();
			ft = m_optimizer.transform(ft);
		}
		return ft.getSMTTerm();
	}
	
	public Map<TermVariable, Term> getAuxVariables() {
		return m_auxVariables;
	}
	
	public void setProduceModels(boolean produceModels) {
		if (produceModels)
			m_BooleanVars = new ScopedHashSet<BooleanVarAtom>();
	}
	
	public Set<BooleanVarAtom> getBooleanVars() {
		return m_BooleanVars;
	}
	
}
