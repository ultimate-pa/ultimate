/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneer {
	
	private final IUltimateServiceProvider m_Services;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	
	private final LassoUnderConstruction m_Lasso;
	
	private enum Part { STEM, LOOP };
	
	private final NestedMap2<Part, NonTheorySymbol<?>, TransFormulaLR> m_Symbol2OriginalTF = 
			new NestedMap2<Part, NonTheorySymbol<?>, TransFormulaLR>();
	private HashRelation<NonTheorySymbol<?>, Term> m_Symbol2StemConjuncts;
	/**
	 * NonTheorySymbols of stem that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<NonTheorySymbol<?>> m_StemSymbolsWithoutConjuncts;
	private HashRelation<NonTheorySymbol<?>, Term> m_Symbol2LoopConjuncts;
	/**
	 * NonTheorySymbols of loop that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<NonTheorySymbol<?>> m_LoopSymbolsWithoutConjuncts;
	private List<Term> m_StemConjunctsWithoutSymbols;
	private List<Term> m_LoopConjunctsWithoutSymbols;
	private final UnionFind<NonTheorySymbol<?>> m_EquivalentSymbols = new UnionFind<>();
	private Set<RankVar> m_AllRankVars = new HashSet<RankVar>();
	private Script m_Script;
	private final List<LassoUnderConstruction> m_NewLassos = new ArrayList<>();
	
	
	public LassoPartitioneer(IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor, 
			Script script, LassoUnderConstruction lasso) {
		m_Services = services;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
		m_Script = script;
		m_Lasso = lasso;
		doPartition();
	}

	private boolean checkStemImplications() {
		boolean result = true;
		for (LassoUnderConstruction newLasso : m_NewLassos) {
			result &= (LassoUnderConstruction.checkStemImplication(m_Script, m_Lasso, newLasso) != LBool.SAT);
			assert result;
		}
		return result;
	}

	public List<LassoUnderConstruction> getNewLassos() {
		return m_NewLassos;
	}

	private void doPartition() {
		m_Symbol2StemConjuncts = new HashRelation<>();
		m_Symbol2LoopConjuncts = new HashRelation<>();
		m_StemSymbolsWithoutConjuncts = new HashSet<>();
		m_LoopSymbolsWithoutConjuncts = new HashSet<>();
		m_StemConjunctsWithoutSymbols = new ArrayList<>();
		m_LoopConjunctsWithoutSymbols = new ArrayList<>();
		
		extractSymbols(Part.STEM, m_Lasso.getStem(), m_Symbol2StemConjuncts, 
				m_StemSymbolsWithoutConjuncts, m_StemConjunctsWithoutSymbols);
		extractSymbols(Part.LOOP, m_Lasso.getLoop(), m_Symbol2LoopConjuncts, 
				m_LoopSymbolsWithoutConjuncts, m_LoopConjunctsWithoutSymbols);
		
		for (RankVar rv : m_AllRankVars) {
			Set<NonTheorySymbol<?>> symbols = new HashSet<NonTheorySymbol<?>>();
			extractInVarAndOutVarSymbols(rv, symbols, m_Lasso.getStem());
			extractInVarAndOutVarSymbols(rv, symbols, m_Lasso.getLoop()); 
			announceEquivalence(symbols);
		}


		for (NonTheorySymbol<?> equivalenceClassRepresentative : 
								m_EquivalentSymbols.getAllRepresentatives()) {
			Set<NonTheorySymbol<?>> symbolEquivalenceClass = 
					m_EquivalentSymbols.getEquivalenceClassMembers(equivalenceClassRepresentative);
			Set<Term> equivalentStemConjuncts = new HashSet<Term>();
			Set<Term> equivalentLoopConjuncts = new HashSet<Term>();
			Set<NonTheorySymbol<?>> equivalentStemSymbolsWithoutConjunct = new HashSet<NonTheorySymbol<?>>();
			Set<NonTheorySymbol<?>> equivalentLoopSymbolsWithoutConjunct = new HashSet<NonTheorySymbol<?>>();
			for (NonTheorySymbol<?> tv : symbolEquivalenceClass) {
				if (m_Symbol2StemConjuncts.getDomain().contains(tv)) {
					equivalentStemConjuncts.addAll(m_Symbol2StemConjuncts.getImage(tv));
				} else if (m_StemSymbolsWithoutConjuncts.contains(tv)) {
					equivalentStemSymbolsWithoutConjunct.add(tv);
				} else if (m_Symbol2LoopConjuncts.getDomain().contains(tv)) {
					equivalentLoopConjuncts.addAll(m_Symbol2LoopConjuncts.getImage(tv));
				} else if (m_LoopSymbolsWithoutConjuncts.contains(tv)) {
					equivalentLoopSymbolsWithoutConjunct.add(tv);
				} else {
					throw new AssertionError("unknown variable " + tv);
				}
			}
			if (equivalentStemConjuncts.isEmpty() && equivalentStemSymbolsWithoutConjunct.isEmpty() 
					&& equivalentLoopConjuncts.isEmpty() && equivalentLoopSymbolsWithoutConjunct.isEmpty()) {
				// do nothing
			} else {
				TransFormulaLR stemTransformulaLR = constructTransFormulaLR(Part.STEM, equivalentStemConjuncts, equivalentStemSymbolsWithoutConjunct);
				TransFormulaLR loopTransformulaLR = constructTransFormulaLR(Part.LOOP, equivalentLoopConjuncts, equivalentLoopSymbolsWithoutConjunct);
				m_NewLassos.add(new LassoUnderConstruction(stemTransformulaLR, loopTransformulaLR));
			}
		}
		
		if (emptyOrTrue(m_StemConjunctsWithoutSymbols) && emptyOrTrue(m_LoopConjunctsWithoutSymbols)) {
			// do nothing
		} else {
			TransFormulaLR stemTransformulaLR = constructTransFormulaLR(Part.STEM, m_StemConjunctsWithoutSymbols);
			TransFormulaLR loopTransformulaLR = constructTransFormulaLR(Part.LOOP, m_LoopConjunctsWithoutSymbols);
			m_NewLassos.add(new LassoUnderConstruction(stemTransformulaLR, loopTransformulaLR));
		}
	}



	private boolean emptyOrTrue(List<Term> terms) {
		if (terms.isEmpty()) {
			return true;
		} else {
			Term conjunction = SmtUtils.and(m_Script, terms);
			return (conjunction.toString().equals("true"));
		}
	}

	private void extractInVarAndOutVarSymbols(RankVar rv,
			Set<NonTheorySymbol<?>> symbols, TransFormulaLR transFormulaLR) {
		Term inVar = transFormulaLR.getInVars().get(rv);
		if (inVar != null) {
			symbols.add(constructSymbol(inVar));
		}
		Term outVar = transFormulaLR.getOutVars().get(rv);
		if (outVar != null) {
			symbols.add(constructSymbol(outVar));
		}
		assert (inVar == null) == (outVar == null) : "both or none";
	}
	
	private TransFormulaLR constructTransFormulaLR(
			Part part, Set<Term> equivalentConjuncts, Set<NonTheorySymbol<?>> equivalentVariablesWithoutConjunct) {
		TransFormulaLR transformulaLR;
		Term formula = Util.and(m_Script, equivalentConjuncts.toArray(new Term[equivalentConjuncts.size()]));
		transformulaLR = new TransFormulaLR(formula);
		for (NonTheorySymbol<?> symbol : NonTheorySymbol.extractNonTheorySymbols(formula)) {
			addInOuAuxVar(part, transformulaLR, symbol);
		}
		for (NonTheorySymbol<?> symbol : equivalentVariablesWithoutConjunct) {
			addInOuAuxVar(part, transformulaLR, symbol);
		}
		return transformulaLR;
	}
	
	private TransFormulaLR constructTransFormulaLR(
			Part part, List<Term> conjunctsWithoutSymbols) {
		TransFormulaLR transformulaLR;
		Term formula = Util.and(m_Script, conjunctsWithoutSymbols.toArray(new Term[conjunctsWithoutSymbols.size()]));
		transformulaLR = new TransFormulaLR(formula);
		return transformulaLR;
	}


	private void addInOuAuxVar(Part part, TransFormulaLR transformulaLR, NonTheorySymbol<?> symbol) {
		TransFormulaLR original = m_Symbol2OriginalTF.get(part, symbol);
		boolean isConstant;
		Term term;
		if (symbol instanceof NonTheorySymbol.Variable) {
			term = (Term) symbol.getSymbol();
			isConstant = false;
		} else if (symbol instanceof NonTheorySymbol.Constant) {
			term = (Term) symbol.getSymbol();
			isConstant = true;
		} else {
			throw new UnsupportedOperationException("function symbols not yet supported");
		}
		RankVar inVarRankVar = original.getInVarsReverseMapping().get(term);
		RankVar outVarRankVar = original.getOutVarsReverseMapping().get(term);
		boolean isAuxVar = original.getAuxVars().contains(term);
		assert (isConstant || !isAuxVar || (inVarRankVar == null && outVarRankVar == null)) : "auxVar may neither be inVar nor outVar";
		assert (isConstant || !(inVarRankVar == null && outVarRankVar == null) || isAuxVar) : "neither inVar nor outVar may be auxVar";
		if (inVarRankVar != null) {
			transformulaLR.addInVar(inVarRankVar, term);
		}
		if (outVarRankVar != null) {
			transformulaLR.addOutVar(outVarRankVar, term);
		}
		if (isAuxVar) {
			transformulaLR.addAuxVars(Collections.singleton((TermVariable) term));
		}
	}


	private HashRelation<NonTheorySymbol<?>, Term> extractSymbols(
			Part part, TransFormulaLR tf, 
			HashRelation<NonTheorySymbol<?>, Term> symbol2Conjuncts, 
			HashSet<NonTheorySymbol<?>> symbolsWithoutConjuncts,
			List<Term> conjunctsWithoutSymbols) {
		m_AllRankVars.addAll(tf.getInVars().keySet());
		m_AllRankVars.addAll(tf.getOutVars().keySet());
		//FIXME CNF conversion should be done in advance if desired
		Term cnf = (new Cnf(m_Script, m_Services, m_FreshTermVariableConstructor)).transform(tf.getFormula());
		Term[] conjuncts = SmtUtils.getConjuncts(cnf);
		for (Term conjunct : conjuncts) {
			Set<NonTheorySymbol<?>> allSymbolsOfConjunct = NonTheorySymbol.extractNonTheorySymbols(conjunct);
			if (allSymbolsOfConjunct.isEmpty()) {
				conjunctsWithoutSymbols.add(conjunct);
			} else {
				for (NonTheorySymbol<?> symbol : allSymbolsOfConjunct) {
					TransFormulaLR oldValue = m_Symbol2OriginalTF.put(part, symbol, tf);
					assert oldValue == null || oldValue == tf : "may not be modified";
					allSymbolsOfConjunct.add(symbol);
					if (m_EquivalentSymbols.find(symbol) == null) {
						m_EquivalentSymbols.makeEquivalenceClass(symbol);
					}
					symbol2Conjuncts.addPair(symbol, conjunct);
				}
				announceEquivalence(allSymbolsOfConjunct);
			}
		}
		for (Entry<RankVar, Term> entry : tf.getInVars().entrySet()) {
			addIfNotAlreadyAdded(part, symbolsWithoutConjuncts, tf, entry.getValue(), symbol2Conjuncts);
		}
		for (Entry<RankVar, Term> entry : tf.getOutVars().entrySet()) {
			addIfNotAlreadyAdded(part, symbolsWithoutConjuncts, tf, entry.getValue(), symbol2Conjuncts);
		}
		return symbol2Conjuncts;
	}


	private void addIfNotAlreadyAdded(
			Part part, HashSet<NonTheorySymbol<?>> symbolsWithoutConjuncts, TransFormulaLR tf,
			Term tvOrConstant,
			HashRelation<NonTheorySymbol<?>, Term> symbol2Conjuncts) {
		NonTheorySymbol<?> symbol = constructSymbol(tvOrConstant);
		if (!symbol2Conjuncts.getDomain().contains(symbol) && !symbolsWithoutConjuncts.contains(symbol)) {
			if (m_EquivalentSymbols.find(symbol) == null) {
				// check needed because constants may occur in stem and loop.
				m_EquivalentSymbols.makeEquivalenceClass(symbol);
			}
			symbolsWithoutConjuncts.add(symbol);
			TransFormulaLR oldValue = m_Symbol2OriginalTF.put(part, symbol, tf);
			assert oldValue == null || oldValue == tf : "may not be modified";
		}
	}


	private NonTheorySymbol<?> constructSymbol(Term tvOrConstant) {
		if (tvOrConstant instanceof TermVariable) {
			return new NonTheorySymbol.Variable((TermVariable) tvOrConstant);
		} else {
			if (SmtUtils.isConstant(tvOrConstant)) {
				return new NonTheorySymbol.Constant((ApplicationTerm) tvOrConstant);
			} else {
				throw new IllegalArgumentException();
			}
		}
	}


	private void announceEquivalence(Set<NonTheorySymbol<?>> allSymbolsOfConjunct) {
		NonTheorySymbol<?> last = null;
		for (NonTheorySymbol<?> symbol : allSymbolsOfConjunct) {
			if (last != null) {
				m_EquivalentSymbols.union(symbol, last);
			}
			last = symbol;
		}
	}

}
