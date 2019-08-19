/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneer {
	
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	
	private final LassoUnderConstruction mLasso;
	
	private enum Part { STEM, LOOP };
	
	private final NestedMap2<Part, NonTheorySymbol<?>, ModifiableTransFormula> mSymbol2OriginalTF = 
			new NestedMap2<Part, NonTheorySymbol<?>, ModifiableTransFormula>();
	private HashRelation<NonTheorySymbol<?>, Term> mSymbol2StemConjuncts;
	/**
	 * NonTheorySymbols of stem that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<NonTheorySymbol<?>> mStemSymbolsWithoutConjuncts;
	private HashRelation<NonTheorySymbol<?>, Term> mSymbol2LoopConjuncts;
	/**
	 * NonTheorySymbols of loop that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<NonTheorySymbol<?>> mLoopSymbolsWithoutConjuncts;
	private List<Term> mStemConjunctsWithoutSymbols;
	private List<Term> mLoopConjunctsWithoutSymbols;
	private final UnionFind<NonTheorySymbol<?>> mEquivalentSymbols = new UnionFind<>();
	private final Set<IProgramVar> mAllRankVars = new HashSet<IProgramVar>();
	private final List<LassoUnderConstruction> mNewLassos = new ArrayList<>();
	private final XnfConversionTechnique mXnfConversionTechnique;
	
	
	public LassoPartitioneer(final IUltimateServiceProvider services, 
			final ManagedScript mgdScript, 
			final LassoUnderConstruction lasso, 
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mMgdScript = mgdScript;
		mLasso = lasso;
		mXnfConversionTechnique = xnfConversionTechnique;
		doPartition();
//		assert checkStemImplications() : "stem problem";
	}

//	private boolean checkStemImplications() {
//		boolean result = true;
//		for (LassoUnderConstruction newLasso : mNewLassos) {
//			result &= checkStemImplication(newLasso);
//			assert result;
//		}
//		return result;
//	}
//	
//	private boolean checkStemImplication(LassoUnderConstruction newLasso) {
//		boolean result = TransFormulaUtils.implies(mLasso.getStem(), newLasso.getStem(), mScript, 
//				mBoogie2Smt.getBoogie2SmtSymbolTable(), 
//				mBoogie2Smt.getVariableManager()) != LBool.SAT;
//		return result;
//	}

	public List<LassoUnderConstruction> getNewLassos() {
		return mNewLassos;
	}

	private void doPartition() {
		mSymbol2StemConjuncts = new HashRelation<>();
		mSymbol2LoopConjuncts = new HashRelation<>();
		mStemSymbolsWithoutConjuncts = new HashSet<>();
		mLoopSymbolsWithoutConjuncts = new HashSet<>();
		mStemConjunctsWithoutSymbols = new ArrayList<>();
		mLoopConjunctsWithoutSymbols = new ArrayList<>();
		
		extractSymbols(Part.STEM, mLasso.getStem(), mSymbol2StemConjuncts, 
				mStemSymbolsWithoutConjuncts, mStemConjunctsWithoutSymbols);
		extractSymbols(Part.LOOP, mLasso.getLoop(), mSymbol2LoopConjuncts, 
				mLoopSymbolsWithoutConjuncts, mLoopConjunctsWithoutSymbols);
		
		for (final IProgramVar rv : mAllRankVars) {
			final Set<NonTheorySymbol<?>> symbols = new HashSet<NonTheorySymbol<?>>();
			extractInVarAndOutVarSymbols(rv, symbols, mLasso.getStem());
			extractInVarAndOutVarSymbols(rv, symbols, mLasso.getLoop()); 
			announceEquivalence(symbols);
		}


		for (final NonTheorySymbol<?> equivalenceClassRepresentative : 
								mEquivalentSymbols.getAllRepresentatives()) {
			final Set<NonTheorySymbol<?>> symbolEquivalenceClass = 
					mEquivalentSymbols.getEquivalenceClassMembers(equivalenceClassRepresentative);
			final Set<Term> equivalentStemConjuncts = new HashSet<Term>();
			final Set<Term> equivalentLoopConjuncts = new HashSet<Term>();
			final Set<NonTheorySymbol<?>> equivalentStemSymbolsWithoutConjunct = new HashSet<NonTheorySymbol<?>>();
			final Set<NonTheorySymbol<?>> equivalentLoopSymbolsWithoutConjunct = new HashSet<NonTheorySymbol<?>>();
			for (final NonTheorySymbol<?> tv : symbolEquivalenceClass) {
				if (mSymbol2StemConjuncts.getDomain().contains(tv)) {
					equivalentStemConjuncts.addAll(mSymbol2StemConjuncts.getImage(tv));
				} else if (mStemSymbolsWithoutConjuncts.contains(tv)) {
					equivalentStemSymbolsWithoutConjunct.add(tv);
				} else if (mSymbol2LoopConjuncts.getDomain().contains(tv)) {
					equivalentLoopConjuncts.addAll(mSymbol2LoopConjuncts.getImage(tv));
				} else if (mLoopSymbolsWithoutConjuncts.contains(tv)) {
					equivalentLoopSymbolsWithoutConjunct.add(tv);
				} else {
					throw new AssertionError("unknown variable " + tv);
				}
			}
			if (equivalentStemConjuncts.isEmpty() && equivalentStemSymbolsWithoutConjunct.isEmpty() 
					&& equivalentLoopConjuncts.isEmpty() && equivalentLoopSymbolsWithoutConjunct.isEmpty()) {
				// do nothing
			} else {
				final ModifiableTransFormula stemTransformulaLR = constructTransFormulaLR(Part.STEM, equivalentStemConjuncts, equivalentStemSymbolsWithoutConjunct);
				final ModifiableTransFormula loopTransformulaLR = constructTransFormulaLR(Part.LOOP, equivalentLoopConjuncts, equivalentLoopSymbolsWithoutConjunct);
				mNewLassos.add(new LassoUnderConstruction(stemTransformulaLR, loopTransformulaLR));
			}
		}
		
		if (emptyOrTrue(mStemConjunctsWithoutSymbols) && emptyOrTrue(mLoopConjunctsWithoutSymbols)) {
			// do nothing
		} else {
			final ModifiableTransFormula stemTransformulaLR = constructTransFormulaLR(Part.STEM, mStemConjunctsWithoutSymbols);
			final ModifiableTransFormula loopTransformulaLR = constructTransFormulaLR(Part.LOOP, mLoopConjunctsWithoutSymbols);
			mNewLassos.add(new LassoUnderConstruction(stemTransformulaLR, loopTransformulaLR));
		}
	}



	private boolean emptyOrTrue(final List<Term> terms) {
		if (terms.isEmpty()) {
			return true;
		} else {
			final Term conjunction = SmtUtils.and(mMgdScript.getScript(), terms);
			return (conjunction.toString().equals("true"));
		}
	}

	private void extractInVarAndOutVarSymbols(final IProgramVar rv,
			final Set<NonTheorySymbol<?>> symbols, final ModifiableTransFormula transFormulaLR) {
		final Term inVar = transFormulaLR.getInVars().get(rv);
		if (inVar != null) {
			symbols.add(constructSymbol(inVar));
		}
		final Term outVar = transFormulaLR.getOutVars().get(rv);
		if (outVar != null) {
			symbols.add(constructSymbol(outVar));
		}
		assert (inVar == null) == (outVar == null) : "both or none";
	}
	
	private ModifiableTransFormula constructTransFormulaLR(
			final Part part, final Set<Term> equivalentConjuncts, final Set<NonTheorySymbol<?>> equivalentVariablesWithoutConjunct) {
		ModifiableTransFormula transformulaLR;
		final Term formula = SmtUtils.and(mMgdScript.getScript(), equivalentConjuncts.toArray(new Term[equivalentConjuncts.size()]));
		transformulaLR = new ModifiableTransFormula(formula);
		for (final NonTheorySymbol<?> symbol : NonTheorySymbol.extractNonTheorySymbols(formula)) {
			addInOuAuxVar(part, transformulaLR, symbol);
		}
		for (final NonTheorySymbol<?> symbol : equivalentVariablesWithoutConjunct) {
			addInOuAuxVar(part, transformulaLR, symbol);
		}
		return transformulaLR;
	}
	
	private ModifiableTransFormula constructTransFormulaLR(
			final Part part, final List<Term> conjunctsWithoutSymbols) {
		ModifiableTransFormula transformulaLR;
		final Term formula = SmtUtils.and(mMgdScript.getScript(), conjunctsWithoutSymbols.toArray(new Term[conjunctsWithoutSymbols.size()]));
		transformulaLR = new ModifiableTransFormula(formula);
		return transformulaLR;
	}


	private void addInOuAuxVar(final Part part, final ModifiableTransFormula transformulaLR, final NonTheorySymbol<?> symbol) {
		final ModifiableTransFormula original = mSymbol2OriginalTF.get(part, symbol);
		boolean isConstant;
		TermVariable term;
		if (symbol instanceof NonTheorySymbol.Variable) {
			term = (TermVariable) symbol.getSymbol();
			isConstant = false;
		} else if (symbol instanceof NonTheorySymbol.Constant) {
			term = (TermVariable) symbol.getSymbol();
			isConstant = true;
		} else {
			throw new UnsupportedOperationException("function symbols not yet supported");
		}
		final IProgramVar inVarRankVar = original.getInVarsReverseMapping().get(term);
		final IProgramVar outVarRankVar = original.getOutVarsReverseMapping().get(term);
		final boolean isAuxVar = original.getAuxVars().contains(term);
		assert (isConstant || !isAuxVar || (inVarRankVar == null && outVarRankVar == null)) : "auxVar may neither be inVar nor outVar";
		assert (isConstant || !(inVarRankVar == null && outVarRankVar == null) || isAuxVar) : "neither inVar nor outVar may be auxVar";
		if (inVarRankVar != null) {
			transformulaLR.addInVar(inVarRankVar, term);
		}
		if (outVarRankVar != null) {
			transformulaLR.addOutVar(outVarRankVar, term);
		}
		if (isAuxVar) {
			final TermVariable auxVarTv = term;
			transformulaLR.addAuxVars(Collections.singleton(auxVarTv));
		}
	}


	private HashRelation<NonTheorySymbol<?>, Term> extractSymbols(
			final Part part, final ModifiableTransFormula tf, 
			final HashRelation<NonTheorySymbol<?>, Term> symbol2Conjuncts, 
			final HashSet<NonTheorySymbol<?>> symbolsWithoutConjuncts,
			final List<Term> conjunctsWithoutSymbols) {
		mAllRankVars.addAll(tf.getInVars().keySet());
		mAllRankVars.addAll(tf.getOutVars().keySet());
		//FIXME CNF conversion should be done in advance if desired
		final Term cnf = SmtUtils.toCnf(mServices, mMgdScript, tf.getFormula(), mXnfConversionTechnique);
		final Term[] conjuncts = SmtUtils.getConjuncts(cnf);
		for (final Term conjunct : conjuncts) {
			final Set<NonTheorySymbol<?>> allSymbolsOfConjunct = NonTheorySymbol.extractNonTheorySymbols(conjunct);
			if (allSymbolsOfConjunct.isEmpty()) {
				conjunctsWithoutSymbols.add(conjunct);
			} else {
				for (final NonTheorySymbol<?> symbol : allSymbolsOfConjunct) {
					final ModifiableTransFormula oldValue = mSymbol2OriginalTF.put(part, symbol, tf);
					assert oldValue == null || oldValue == tf : "may not be modified";
					allSymbolsOfConjunct.add(symbol);
					if (mEquivalentSymbols.find(symbol) == null) {
						mEquivalentSymbols.makeEquivalenceClass(symbol);
					}
					symbol2Conjuncts.addPair(symbol, conjunct);
				}
				announceEquivalence(allSymbolsOfConjunct);
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			addIfNotAlreadyAdded(part, symbolsWithoutConjuncts, tf, entry.getValue(), symbol2Conjuncts);
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			addIfNotAlreadyAdded(part, symbolsWithoutConjuncts, tf, entry.getValue(), symbol2Conjuncts);
		}
		return symbol2Conjuncts;
	}


	private void addIfNotAlreadyAdded(
			final Part part, final HashSet<NonTheorySymbol<?>> symbolsWithoutConjuncts, final ModifiableTransFormula tf,
			final Term tvOrConstant,
			final HashRelation<NonTheorySymbol<?>, Term> symbol2Conjuncts) {
		final NonTheorySymbol<?> symbol = constructSymbol(tvOrConstant);
		if (!symbol2Conjuncts.getDomain().contains(symbol) && !symbolsWithoutConjuncts.contains(symbol)) {
			if (mEquivalentSymbols.find(symbol) == null) {
				// check needed because constants may occur in stem and loop.
				mEquivalentSymbols.makeEquivalenceClass(symbol);
			}
			symbolsWithoutConjuncts.add(symbol);
			final ModifiableTransFormula oldValue = mSymbol2OriginalTF.put(part, symbol, tf);
			assert oldValue == null || oldValue == tf : "may not be modified";
		}
	}


	private NonTheorySymbol<?> constructSymbol(final Term tvOrConstant) {
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


	private void announceEquivalence(final Set<NonTheorySymbol<?>> allSymbolsOfConjunct) {
		NonTheorySymbol<?> last = null;
		for (final NonTheorySymbol<?> symbol : allSymbolsOfConjunct) {
			if (last != null) {
				mEquivalentSymbols.union(symbol, last);
			}
			last = symbol;
		}
	}

}
