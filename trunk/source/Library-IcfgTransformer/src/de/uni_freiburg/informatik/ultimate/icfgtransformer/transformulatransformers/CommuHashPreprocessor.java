/*
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

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;


/**
 * Use CommuhashNormalForm to simplify TransformulaLR
 * 
 * @author Matthias Heizmann.
 */
public class CommuHashPreprocessor extends TransitionPreprocessor {
	private final IUltimateServiceProvider mServices;
	
	public static final String DESCRIPTION = "Simplify formula using CommuhashNormalForm";
	
	public CommuHashPreprocessor(final IUltimateServiceProvider services) {
		super();
		mServices = services;
	}
	
	@Override
	public String getDescription() {
		return DESCRIPTION;
	}
	
	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		return true;
	}
	
	@Override
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf) throws TermException {
		final Term normalized1 = (new ConstantTermNormalizer2()).transform(tf.getFormula());
		final Term normalized2 = (new CommuhashNormalForm(mServices, script.getScript())).transform(normalized1);
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
		protected void convert(final Term term) {
			if (term instanceof ConstantTerm) {
				final ConstantTerm ct = (ConstantTerm) term;
				if (ct.getValue() instanceof BigInteger) {
					final Rational rat = Rational.valueOf(
							(BigInteger) ct.getValue(), BigInteger.ONE); 
					setResult(rat.toTerm(term.getSort()));
				} else if (ct.getValue() instanceof BigDecimal) {
					final BigDecimal decimal = (BigDecimal) ct.getValue();
					Rational rat;
					if (decimal.scale() <= 0) {
						final BigInteger num = decimal.toBigInteger();
						rat = Rational.valueOf(num, BigInteger.ONE);
					} else {
						final BigInteger num = decimal.unscaledValue();
						final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
						rat = Rational.valueOf(num, denom);
					}
					setResult(rat.toTerm(term.getSort()));
				} else if (ct.getValue() instanceof Rational) {
					setResult(ct);
				} else {
					setResult(term);
				}
			} else {
				super.convert(term);
			}
		}
		
	}
}
