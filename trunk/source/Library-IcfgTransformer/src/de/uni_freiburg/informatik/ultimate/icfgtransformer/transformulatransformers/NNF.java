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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Convert a formula into negation normal form.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class NNF extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Transform into negation normal form";

	private final IUltimateServiceProvider mServices;

	public NNF(final IUltimateServiceProvider services) {
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
		final Term oldTerm = oldTF.getFormula();
		final Term newTerm = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script, script.term("distinct", oldTerm, newTerm));
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf)
			throws TermException {
		final Term dnf = SmtUtils.toNnf(mServices, script, tf.getFormula());
		tf.setFormula(dnf);
		return tf;
	}
}
