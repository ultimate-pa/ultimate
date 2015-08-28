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

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;


/**
 * Use SimplifyDDA to simplify TransformulaLR
 * 
 * @author Matthias Heizmann.
 */
public class SimplifyPreprocessor extends TransitionPreprocessor {
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage m_Storage;
	private final boolean m_UseSMTInterpolForSimplification = !true;
	
	public static final String s_Description = "Simplify formula using SimplifyDDA";
	
	public SimplifyPreprocessor(IUltimateServiceProvider services, IToolchainStorage storage) {
		super();
		mServices = services;
		m_Storage = storage;
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
		final Term simplified;
		if (m_UseSMTInterpolForSimplification) {
			Settings settings = new SolverBuilder.Settings(false, "", 10 * 1000, null, false, null, null);
			Script simplificationScript = SolverBuilder.buildScript(mServices, m_Storage, settings);
			simplificationScript.setLogic(Logics.QF_UFLIRA);
			TermTransferrer towards = new TermTransferrer(simplificationScript);
			Term foreign = towards.transform(tf.getFormula());
			Term foreignsimplified = SmtUtils.simplify(simplificationScript, foreign, mServices);
			simplificationScript.exit();
			TermTransferrer back = new TermTransferrer(script);
			simplified = back.transform(foreignsimplified);
		} else {
			simplified = SmtUtils.simplify(script, tf.getFormula(), mServices);
		}
		tf.setFormula(simplified);
		return tf;
	}
}