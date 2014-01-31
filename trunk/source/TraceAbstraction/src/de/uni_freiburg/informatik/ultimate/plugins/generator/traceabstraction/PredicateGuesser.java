package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker.SymbolVisitor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


public class PredicateGuesser {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	static final boolean NON_STRICT_EQUALITIES = true; 
	private final Smt2Boogie m_BoogieVar2SmtVar;
	private final SmtManager m_SmtManager;
	private final ModifiableGlobalVariableManager m_ModGlobVarManager;
	private PredicateExtractor m_pe;
	public PredicateGuesser(SmtManager m_SmtManager, ModifiableGlobalVariableManager modGlobVarManager) {
		super();
		this.m_SmtManager = m_SmtManager;
		this.m_BoogieVar2SmtVar = m_SmtManager.getSmt2Boogie();
		this.m_ModGlobVarManager = modGlobVarManager;
	}
	
	public IPredicate[] extractPredicates(NestedWord<CodeBlock> m_NestedWord){
		m_pe = new PredicateExtractor();
		
		for (int i=0; i<m_NestedWord.length(); i++) {
			CodeBlock block = m_NestedWord.getSymbol(i);
			m_pe.extractPredicates(block.getTransitionFormula());
			if (m_NestedWord.isCallPosition(i)) {
				Call call = (Call) m_NestedWord.getSymbol(i);
				String proc = call.getCallStatement().getMethodName();
				TransFormula oldVarsAssignment = 
						m_ModGlobVarManager.getOldVarsAssignment(proc);
				m_pe.extractPredicates(oldVarsAssignment);
			}
		}
		
		PredicateSet ps = m_pe.m_P;
		ps  = ps.substituteFreeVars();
		
		IPredicate[] result = ps.getPredicates();
		int i=0;
		for (IPredicate p : result) {
			s_Logger.debug(new DebugMessage("GuessedPredicate{0}: {1}", i++, p));
		}
		return result;
		
	}
	
	
	
	private class PredicateSet {
		private final Smt2Boogie m_BoogieVar2SmtVar;
		private final Script m_Scipt;
		private BinaryRelations m_Equal = new BinaryRelations("=");
		private BinaryRelations m_Leq = new BinaryRelations("<=");
		private BinaryRelations m_L = new BinaryRelations("<");
		private Set<Term> m_Others = new HashSet<Term>();

		
		/**
		 * @param boogieVar2SmtVar
		 */
		public PredicateSet(Smt2Boogie boogieVar2SmtVar) {
			m_BoogieVar2SmtVar = boogieVar2SmtVar;
			m_Scipt = boogieVar2SmtVar.getScript();
		}

		void equal(Term t1, Term t2) {
			assert (t1 != null);
			assert (t2 != null);
			m_Equal.add(t1,t2);
			m_Equal.add(t2,t1);

		}
		
		void leq(Term t1, Term t2) {
			m_Leq.add(t1,t2);
		}
		
		void l(Term t1, Term t2) {
			m_L.add(t1, t2);
		}
		public void add(Term term) {
			LBool sat;
			sat = m_SmtManager.checkSatWithFreeVars(term);
			if (sat == LBool.UNSAT) {
				// predicate is equivalent to false
				return;
			}
			Term negation = m_Scipt.term("not", term);
			sat = m_SmtManager.checkSatWithFreeVars(negation);
			if (sat == LBool.UNSAT) {
				// predicate is equivalent to true
				return;
			}
			m_Others.add(term);
		}
		int size() {
			return m_Equal.size() + m_Leq.size() + m_L.size() + m_Others.size();
		}
		
		public IPredicate[] getPredicates() {
			List<Term> asTerms = new ArrayList<Term>();
			for (Term fst : m_L.getFsts()) {
				for (Term snd : m_L.getSnds(fst)) {
					Term term = m_Scipt.term("<", fst, snd);
					if (termIsNeitherTrueNorFalse(term)) {
						asTerms.add(term);
					}
				}
			}
			for (Term fst : m_Leq.getFsts()) {
				for (Term snd : m_Leq.getSnds(fst)) {
					Term term = m_Scipt.term("<=", fst, snd);
					if (termIsNeitherTrueNorFalse(term)) {
						asTerms.add(term);
					}
				}
			}
			BinaryRelations addedEqualities = new BinaryRelations("=");
			for (Term fst : m_Equal.getFsts()) {
				for (Term snd : m_Equal.getSnds(fst)) {
					if (NON_STRICT_EQUALITIES) {
						Sort intSort = m_Scipt.sort("Int");
						Sort realSort = m_Scipt.sort("Real");
						Sort keySort = fst.getSort();
						if (keySort == intSort || keySort == realSort) {
							Term term = m_Scipt.term("<=", fst, snd);
							if (termIsNeitherTrueNorFalse(term)) {
								asTerms.add(term);
							}
						}
					}
					else {
						if (addedEqualities.contains(snd,fst)) {
							// symmetric pair already added, do nothing
						}
						else {
							Term term = m_Scipt.term("=", fst, snd);
							if (termIsNeitherTrueNorFalse(term)) {
								asTerms.add(term);
							}
							addedEqualities.add(fst,snd);
						}
					}
				}
			}
			asTerms.addAll(m_Others);
			IPredicate[] result = new IPredicate[asTerms.size()];
			int i=0;
			for (Term term : asTerms) {
				SmtManager.TermVarsProc tvp = m_SmtManager.computeTermVarsProc(term);
				result[i] = m_SmtManager.newPredicate(term, tvp.getProcedures(),
						tvp.getVars(), tvp.getClosedFormula());
				i++;
			}
			return result;
		}
		
		private boolean termIsNeitherTrueNorFalse(Term negation) {
			LBool sat;
			sat = m_SmtManager.checkSatWithFreeVars(negation);
			if (sat == LBool.UNSAT) {
				// predicate is equivalent to false
				return false;
			}
			negation = m_Scipt.term("not", negation);
			sat = m_SmtManager.checkSatWithFreeVars(negation);
			if (sat == LBool.UNSAT) {
				// predicate is equivalent to true
				return false;
			}
			return true;
		}
		
		private class BinaryRelations {
			private final String m_Funcname;
			public BinaryRelations(String funcname) {
				this.m_Funcname = funcname;
			}
			public String getFuncname() {
				return m_Funcname;
			}
			Map<Term,Set<Term>> m_Map = new HashMap<Term,Set<Term>>();
			public void add(Term fst, Term snd) {
				Set<Term> snds = m_Map.get(fst);
				if (snds == null ) {
					snds = new HashSet<Term>();
					m_Map.put(fst, snds);
				}
				snds.add(snd);
			}

			public boolean contains(Term fst, Term snd) {
				Set<Term> snds = m_Map.get(fst);
				if (snds == null) {
					return false;
				}
				else {
					return snds.contains(snd);
				}
			}
			public Set<Term> getFsts() {
				return m_Map.keySet();
			}
			public Set<Term> getSnds(Term fst) {
				Set<Term> snds = m_Map.get(fst);
				if (snds == null) {
					return new HashSet<Term>(0);
				}
				else {
					return snds;
				}
			}
			@Override
			public String toString() {
				return m_Map.toString();
			}
			public int size() {
				int result = 0;
				for (Term term : getFsts()) {
					result += getSnds(term).size();
				}
			return result;
			}
		}
		
		public PredicateSet substituteFreeVars() {
			PredicateSet result = new PredicateSet(m_BoogieVar2SmtVar);
			result.m_Equal = substituteFreeVars(m_Equal, m_Equal);
			result.m_Leq = substituteFreeVars(m_Leq, m_Equal);
			result.m_L = substituteFreeVars(m_L, m_Equal);
			for (Term term : m_Others) {
				for (Term substitute : substituteFreeVars(term, m_Equal)){
					result.add(substitute);
				}
			}
			s_Logger.warn("Before: " + this.size() + " predicates");
			s_Logger.warn("After: " + result.size() + " predicates");
			return result;
			
		}
		
		private BinaryRelations substituteFreeVars(BinaryRelations op, BinaryRelations equalities) {
			BinaryRelations result = new BinaryRelations(op.getFuncname());
			for (Term fst : op.getFsts()) {
				for (Term snd : op.getSnds(fst)) {
					Set<Term> fstSubstituents = substituteFreeVars(fst, equalities);
					Set<Term> sndSubstituents = substituteFreeVars(snd, equalities);
					for (Term fstSub : fstSubstituents) {
						for (Term sndSub : sndSubstituents) {
							result.add(fstSub, sndSub);
						}
					}
					
				}
				
			}
			return result;
		}
		
		private Set<Term> substituteFreeVars(Term term, BinaryRelations equalities) {
			Set<Term> result = new HashSet<Term>();
			result.add(term);
			TermVariable[] freeVars = term.getFreeVars();
			for (TermVariable tv : freeVars) {
				for (Term substitute : equalities.getSnds(tv)) {
					TermVariable[] vars = { tv };
					Term[] values = { substitute };
					Term substTerm = m_Scipt.let(vars, values, term);
					Term unlet = (new FormulaUnLet()).unlet(substTerm);
					result.add(unlet);
				}
			}
			return result;
		}
	}
	
	
	
	
	
	private class PredicateExtractor implements SymbolVisitor {
		private PredicateSet m_P = new PredicateSet(m_BoogieVar2SmtVar);

		public void extractPredicates(TransFormula tf) {
			Term term = tf.getFormula();
			term = substituteVarsByUnindexedVars(term, tf.getInVars());
			term = substituteVarsByUnindexedVars(term, tf.getOutVars());
			term = (new FormulaUnLet()).unlet(term);
			FormulaWalker fw = new FormulaWalker(this, m_SmtManager.getScript());
			fw.process(term);
		}
		
		
		/**
		 * Let all vars occuring in a BoogieVar2TermVariable map to the 
		 * non-index TermVariable for the BoogieVar.
		 */
		private Term substituteVarsByUnindexedVars(Term input, Map<BoogieVar,TermVariable> map) {
			TermVariable[] vars = new TermVariable[map.size()];
			Term[] values = new Term[map.size()];
			int offset = 0;
			for (BoogieVar var : map.keySet()) {
				vars[offset] = map.get(var);
				values[offset] = var.getTermVariable();
				offset++;
			}
			return m_SmtManager.getScript().let(vars, values, input);
		}
		

		@Override
		public Term term(Term input) {
			Sort boolSort = m_SmtManager.getScript().sort("Bool");
			if (input.getSort() !=  boolSort) {
				throw new IllegalArgumentException("Transition formulas must" +
						" have Boolean sort");
			}
			if (input instanceof QuantifiedFormula || input instanceof TermVariable) {
				m_P.m_Others.add(input);
				return input;
			}
			if (!(input instanceof ApplicationTerm)) {
				throw new IllegalArgumentException();
			}
			ApplicationTerm term = (ApplicationTerm) input;
			FunctionSymbol symb = term.getFunction();
			if (symb.getName().equals("=") && !allParamHaveSort(symb,boolSort)) {
				if (term.getParameters().length != 2) {
					throw new UnsupportedOperationException();
				}
				m_P.equal(term.getParameters()[0],term.getParameters()[1]);
				return term;
			} else if (symb.getName().equals("<=") && !allParamHaveSort(symb,boolSort)) {
				if (term.getParameters().length != 2) {
					throw new UnsupportedOperationException();
				}
				m_P.leq(term.getParameters()[0], 
						  term.getParameters()[1]);
				return term;
			} else if (symb.getName().equals(">=") && !allParamHaveSort(symb,boolSort)) {
				if (term.getParameters().length != 2) {
					throw new UnsupportedOperationException();
				}
				m_P.leq(term.getParameters()[1], 
						  term.getParameters()[0]);
				return term;
			} else if (symb.getName().equals("<")) {
				m_P.l(term.getParameters()[0], 
						  term.getParameters()[1]);
				return term;
			} else if (symb.getName().equals(">")) {
				m_P.l(term.getParameters()[1], 
						  term.getParameters()[0]);
				return term;
			} 
			if (!symb.getName().equals("and")) {
				m_P.m_Others.add(term);
			}
			if (allParamHaveSort(symb, boolSort)) {
				//descend into formula
				return null;
			}
			else {
				return term;
			}
		}		

		private  boolean allParamHaveSort(FunctionSymbol symb, Sort sort) {
			for (int i=0; i<symb.getParameterCount(); i++) {
				if (symb.getParameterSort(i) != sort) {
					return false;
				}
			}
			return true;
		}

		@Override
		public void done(Term input) {
			//throw new UnsupportedOperationException();
		}

		@Override
		public boolean unflet() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean unlet() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void let(TermVariable[] tv, Term[] mval) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void quantifier(TermVariable[] tvs) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void endscope(TermVariable[] tv) {
			throw new UnsupportedOperationException();
		}
		
	}
}
