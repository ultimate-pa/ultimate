/*
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Use SimplifyDDA to simplify TransformulaLR
 *
 * @author Matthias Heizmann.
 */
public class SimplifyPreprocessor extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Simplify formula using SimplifyDDA";
	private static final boolean USE_SMTINTERPOL_FOR_SIMPLIFICATION = !true;

	private final IUltimateServiceProvider mServices;

	private final SimplificationTechnique mXnfConversionTechnique;

	public SimplifyPreprocessor(final IUltimateServiceProvider services,
			final SimplificationTechnique xnfConversionTechnique) {
		super();
		mServices = services;
		mXnfConversionTechnique = xnfConversionTechnique;
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
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf)
			throws TermException {
		final Term simplified;
		if (USE_SMTINTERPOL_FOR_SIMPLIFICATION) {
			final SolverSettings settings =
					new SolverBuilder.SolverSettings(false, false, "", 10 * 1000, null, false, null, null);
			final Script simplificationScript = SolverBuilder.buildScript(mServices, settings);
			simplificationScript.setLogic(Logics.QF_UFLIRA);
			final TermTransferrer towards = new TermTransferrer(simplificationScript);
			final Term foreign = towards.transform(tf.getFormula());
			final Term foreignsimplified = SmtUtils.simplify(script, foreign, mServices, mXnfConversionTechnique);
			simplificationScript.exit();
			final TermTransferrer back = new TermTransferrer(script.getScript());
			simplified = back.transform(foreignsimplified);
		} else {
			simplified = SmtUtils.simplify(script, tf.getFormula(), mServices, mXnfConversionTechnique);
		}
		tf.setFormula(simplified);
		return tf;
	}
}
