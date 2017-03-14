/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * 
 * @author Matthias Heizmann
 */
public class ModuloNeighborTransformation extends TransformerPreprocessor {
	public static final String DESCRIPTION = "Replace modulo operation by disjunction if divisor is a literal";

	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of auxiliary variables.
	 */
	private static final boolean CHECK_RESULT = true;

	private final boolean mUseNeibors;

	/**
	 * Constructor
	 */
	public ModuloNeighborTransformation(final boolean useNeibors) {
		super();
		mUseNeibors = useNeibors;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf) throws TermException {
		return super.process(script, tf);
	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		return !(CHECK_RESULT && isIncorrect(script, oldTF.getFormula(), newTF.getFormula()));
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For
	 * this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(final Script script, final Term input, final Term result) {
		return LBool.SAT == Util.checkSat(script, script.term("distinct", input, result));
	}

	@Override
	protected TermTransformer getTransformer(final ManagedScript script) {
		return new ModuloNeighborTransformer(script.getScript());
	}

	/**
	 * Replace integer division and modulo by auxiliary variables and add
	 * definitions of these auxiliary variables.
	 */
	private class ModuloNeighborTransformer extends TermTransformer {
		private final Script mScript;

		ModuloNeighborTransformer(final Script script) {
			assert script != null;
			mScript = script;
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String func = appTerm.getFunction().getName();
			if (func.equals("mod")) {
				assert appTerm.getParameters().length == 2;
				final Term dividend = newArgs[0];
				final Term divisor = newArgs[1];
				if (divisor instanceof ConstantTerm) {
					final Term result;
					final Term inRange;
					{
						final Term geqZero = mScript.term("<=", mScript.numeral(BigInteger.ZERO), dividend);
						final Term lgtDivisor = mScript.term("<", dividend, divisor);
						inRange = mScript.term("and", geqZero, lgtDivisor);
					}
					if (mUseNeibors) {
						Term leftInterval;
						{
							final Term geqleftBound = mScript.term("<=", mScript.term("-", divisor), dividend);
							final Term lgtZero = mScript.term("<", dividend, divisor);
							leftInterval = mScript.term("and", geqleftBound, lgtZero);
						}
						final Term resultForLeftInterval = mScript.term("+", dividend, divisor);

						Term rightInterval;
						{
							final Term geqleftBound = mScript.term("<=", divisor, dividend);
							final Term lgtrightBound = mScript.term("<", dividend, mScript.term("+", divisor, divisor));
							rightInterval = mScript.term("and", geqleftBound, lgtrightBound);
						}
						final Term resultForRightInterval = mScript.term("-", dividend, divisor);
						result = mScript.term("ite", inRange, dividend,
								mScript.term("ite", leftInterval, resultForLeftInterval,
										mScript.term("ite", rightInterval, resultForRightInterval, appTerm)));
					} else {
						result = mScript.term("ite", inRange, dividend, appTerm);
					}
					setResult(result);
					return;

				} else {
					super.convertApplicationTerm(appTerm, newArgs);
					return;
				}
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
		}
	}
}
