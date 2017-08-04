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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * TODO
 * 
 * @author Matthias Heizmann
 * 
 */
public class ArrayAntiDerKiller extends TermTransformer {
	
	private final static String AUX_VAR_PREFIX = "antiDerIndex";
	
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final TermVariable mEliminatee;
	private final int mQuantifier;
	private final List<TermVariable> mNewAuxVars = new ArrayList<>();

	public ArrayAntiDerKiller(final ManagedScript mgdScript, final TermVariable eliminatee, final int quantifier) {
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mEliminatee = eliminatee;
		mQuantifier = quantifier;
	}
	
	
	
	
	

	public List<TermVariable> getNewAuxVars() {
		return mNewAuxVars;
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
						throw new AssertionError("should have been removed by DER");
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						final Term elementwiseEquality = constructElementwiseEquality(lhs, rhs);
						setResult(elementwiseEquality);
						return;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				}
			} else if (fun.equals("distinct")) {
//				throw new AssertionError("distinct should have been removed");
				if (appTerm.getParameters().length != 2) {
					throw new UnsupportedOperationException("only binary equality supported");
				}
				final Term lhs = appTerm.getParameters()[0];
				final Term rhs = appTerm.getParameters()[1];
				if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						final Term elementwiseEquality = constructElementwiseEquality(lhs, rhs);
						final Term result = mScript.term("not", elementwiseEquality);
						setResult(result);
						return;
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						throw new AssertionError("should have been removed by DER");
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
								final Term elementwiseEquality = constructElementwiseEquality(lhs, rhs);
								final Term result = mScript.term("not", elementwiseEquality);
								setResult(result);
								return;
							} else if (mQuantifier == QuantifiedFormula.FORALL) {
								throw new AssertionError("should have been removed by DER");
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




	private Term constructElementwiseEquality(final Term lhsArray, final Term rhsArray) {
		final Sort indexSort = mEliminatee.getSort().getArguments()[0];
		final TermVariable auxIndex = mMgdScript.variable(AUX_VAR_PREFIX, indexSort);
		mNewAuxVars.add(auxIndex);
		final Term lhsSelect = mScript.term("select", lhsArray, auxIndex);
		final Term rhsSelect = mScript.term("select", rhsArray, auxIndex); 
		final Term result = mScript.term("=", lhsSelect, rhsSelect);
		return result;
	}


}
