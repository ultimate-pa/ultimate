/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;


/**
 * Convert a formula into disjunctive normal form, i.e., a formula of the
 * form
 * 
 * <pre>OR ( AND ( NOT? inequality ) )</pre>
 * 
 * This includes a negation normal form (negations only occur before atoms).
 * 
 * @author Jan Leike
 */
public class DNF extends TransitionPreprocessor {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final XnfConversionTechnique mXnfConversionTechnique;
	
	public static final String s_Description = 
			"Transform into disjunctive normal form";
	
	public DNF(final IUltimateServiceProvider services, 
			final ManagedScript freshTermVariableConstructor, 
			final XnfConversionTechnique xnfConversionTechnique) {
		super();
		mServices = services;
		mMgdScript = freshTermVariableConstructor;
		mXnfConversionTechnique = xnfConversionTechnique;
		
	}
	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		final Term old_term = oldTF.getFormula();
		final Term new_term = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script,
				script.term("distinct", old_term, new_term));
	}
	
	@Override
	public ModifiableTransFormula process(final Script script, final ModifiableTransFormula tf) throws TermException {
		final Term dnf = SmtUtils.toDnf(mServices, mMgdScript, tf.getFormula(), mXnfConversionTechnique);
		tf.setFormula(dnf);
		return tf;
	}
}
