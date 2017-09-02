/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * Preprocessor for array partial quantifier elimination that handles
 * DER-like cases.
 *  
 * @author Matthias Heizmann
 * 
 */
public class DerPreprocessor extends TermTransformer {

	private final static String AUX_VAR_PREFIX = "DerPreprocessor";

	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final TermVariable mEliminatee;
	private final int mQuantifier;
	private final List<TermVariable> mNewAuxVars = new ArrayList<>();
	private final ConstructionCache<Term, TermVariable> mAuxVarCc;
	private final List<Term> mAuxVarDefinitions = new ArrayList<>();
	private boolean mIntroducedDerPossibility = false;

	public DerPreprocessor(final IUltimateServiceProvider services, final ManagedScript mgdScript, final TermVariable eliminatee, final int quantifier) {
		mServices = services;
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mEliminatee = eliminatee;
		mQuantifier = quantifier;
		final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

			@Override
			public TermVariable constructValue(final Term term) {
				final TermVariable auxVar = mMgdScript.constructFreshTermVariable(AUX_VAR_PREFIX, term.getSort());
				Term definition = QuantifierUtils.equalityForExists(mScript, mQuantifier, auxVar, term);
				
				//TODO: let Prenex transformer deal with non-NNF terms and remove the following line 
				definition = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(definition);
				
				mAuxVarDefinitions.add(definition);
				mNewAuxVars.add(auxVar);
				return auxVar;
			}
		};
		mAuxVarCc = new ConstructionCache<>(valueConstruction);
	}

	public List<TermVariable> getNewAuxVars() {
		return mNewAuxVars;
	}
	
	
	

	public List<Term> getAuxVarDefinitions() {
		return mAuxVarDefinitions;
	}

	public boolean introducedDerPossibility() {
		return mIntroducedDerPossibility;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String fun = appTerm.getFunction().getName();
			if (fun.equals("=")) {
				if (appTerm.getParameters().length != 2) {
					throw new UnsupportedOperationException("only binary equality supported");
				}
				final Term lhs = appTerm.getParameters()[0];
				final Term rhs = appTerm.getParameters()[1];
				if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						final Term result = do1(lhs, rhs);
						setResult(result);
						return;
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						return;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				}
			} else if (fun.equals("distinct")) {
				// TODO: do not allow distinct after our convention does not allow it nay more
				// throw new AssertionError("distinct should have been removed");
				if (appTerm.getParameters().length != 2) {
					throw new UnsupportedOperationException("only binary equality supported");
				}
				final Term lhs = appTerm.getParameters()[0];
				final Term rhs = appTerm.getParameters()[1];
				if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						return;
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						final Term result = do1(lhs, rhs);
						setResult(result);
						return;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				}
			} else if (fun.equals("not")) {
				assert appTerm.getParameters().length == 1;
				final Term argNot = appTerm.getParameters()[0];
				if (argNot instanceof ApplicationTerm) {
					final ApplicationTerm appTermNot = (ApplicationTerm) argNot;
					if (NonCoreBooleanSubTermTransformer.isCoreBoolean(appTermNot)) {
						throw new AssertionError("should have been transformed to NNF");
					}
					final String funNot = appTermNot.getFunction().getName();
					if (funNot.equals("=")) {
						if (appTermNot.getParameters().length != 2) {
							throw new UnsupportedOperationException("only binary equality supported");
						}
						final Term lhs = appTermNot.getParameters()[0];
						final Term rhs = appTermNot.getParameters()[1];
						if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
							if (mQuantifier == QuantifiedFormula.EXISTS) {
								return;
							} else if (mQuantifier == QuantifiedFormula.FORALL) {
								final Term result = do1(lhs, rhs);
								setResult(result);
								return;
							} else {
								throw new AssertionError("unknown quantifier");
							}
						}
					}
				}
			}
		}

		super.convert(term);
	}

	private Term do1(final Term lhs, final Term rhs) {
		if (lhs.equals(mEliminatee)) {
			return do2(rhs);
		} else if (rhs.equals(mEliminatee)) {
			return do2(lhs);
		} else {
			throw new AssertionError("has to be on one side");
		}
	}

	private Term do2(final Term otherSide) {
		if (!(otherSide instanceof ApplicationTerm)) {
			throw new IllegalArgumentException("expected store, got " + otherSide);
		}
		final ApplicationTerm appTerm = (ApplicationTerm) otherSide;
		if (!appTerm.getFunction().getName().equals("store")) {
			throw new IllegalArgumentException("expected store, got " + otherSide);
		}
		if (appTerm.getParameters().length != 3) {
			throw new IllegalArgumentException("expected store, got " + otherSide);
		}
		return do3(appTerm.getParameters()[0], appTerm.getParameters()[1], appTerm.getParameters()[2]);
		
	}

	private Term do3(final Term array, final Term index, final Term value) {
		final Term newIndex;
		if (Arrays.asList(index.getFreeVars()).contains(mEliminatee)) {
			newIndex = mAuxVarCc.getOrConstruct(index);
		} else {
			newIndex = index;
		}
		final Term newValue;
		if (Arrays.asList(value.getFreeVars()).contains(mEliminatee)) {
			newValue = mAuxVarCc.getOrConstruct(value);
		} else {
			newValue = value;
		}
		Term result;
		if (array.equals(mEliminatee)) {
			// self-update
			final Term select = mScript.term("select", array, newIndex);
			result = QuantifierUtils.equalityForExists(mScript, mQuantifier, select, newValue); 
		} else {
			if (newValue != value || newIndex != index) {
				mIntroducedDerPossibility = true;
			}
			final Term store = mScript.term("store", array, newIndex, newValue);  
			result = QuantifierUtils.equalityForExists(mScript, mQuantifier, mEliminatee, store);
		}
		//TODO: let Prenex transformer deal with non-NNF terms and remove the following line 
		result = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(result);
		return result;
	}

}
