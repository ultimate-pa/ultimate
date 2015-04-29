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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.CommuhashNormalForm;


/**
 * Use CommuhashNormalForm to simplify TransformulaLR
 * 
 * @author Matthias Heizmann.
 */
public class CommuHashPreprocessor extends TransitionPreProcessor {
	private final IUltimateServiceProvider mServices;
	
	public static final String s_Description = "Simplify formula using CommuhashNormalForm";
	
	public CommuHashPreprocessor(IUltimateServiceProvider services) {
		super();
		mServices = services;
	}
	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	protected boolean checkSoundness(Script script, TransFormulaLR oldTF,
			TransFormulaLR newTF) {
		return true;
	}
	
	@Override
	public TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		Term normalized1 = (new ConstantTermNormalizer2()).transform(tf.getFormula());
		Term normalized2 = (new CommuhashNormalForm(mServices, script)).transform(normalized1);
		tf.setFormula(normalized2);
		return tf;
	}
	
	
	
	/* This class was copied from the package.
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.model
	 * FIXME: Proper solution.
	 * 
	 */
	public static class ConstantTermNormalizer2 extends TermTransformer {

		@Override
		protected void convert(Term term) {
			if (term instanceof ConstantTerm) {
				ConstantTerm ct = (ConstantTerm) term;
				if (ct.getValue() instanceof BigInteger) {
					Rational rat = Rational.valueOf(
							(BigInteger) ct.getValue(), BigInteger.ONE); 
					setResult(rat.toTerm(term.getSort()));
				} else if (ct.getValue() instanceof BigDecimal) {
					BigDecimal decimal = (BigDecimal) ct.getValue();
					Rational rat;
					if (decimal.scale() <= 0) {
						BigInteger num = decimal.toBigInteger();
						rat = Rational.valueOf(num, BigInteger.ONE);
					} else {
						BigInteger num = decimal.unscaledValue();
						BigInteger denom = BigInteger.TEN.pow(decimal.scale());
						rat = Rational.valueOf(num, denom);
					}
					setResult(rat.toTerm(term.getSort()));
				} else if (ct.getValue() instanceof Rational)
					setResult(ct);
				else
					setResult(term);
			} else
				super.convert(term);
		}
		
	}
}