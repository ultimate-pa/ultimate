/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneerPreprocessor extends LassoPreprocessor {
	public static final String s_Description = "LassoPartitioneer";
	
	private final IUltimateServiceProvider mServices;
	
	private final ManagedScript mMgdScript;

	private final XnfConversionTechnique mXnfConversionTechnique;

	public LassoPartitioneerPreprocessor(final ManagedScript script, 
			final IUltimateServiceProvider services, 
			final XnfConversionTechnique xnfConversionTechniqe) {
		mServices = services;
		mMgdScript = script;
		mXnfConversionTechnique = xnfConversionTechniqe;
	}

	@Override
	public Collection<LassoUnderConstruction> process(
			final LassoUnderConstruction lasso) throws TermException {
		final LassoPartitioneer lp = new LassoPartitioneer(mServices, mMgdScript, lasso, mXnfConversionTechnique);
		return lp.getNewLassos();
	}


	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	public String getName() {
		return LassoPartitioneer.class.getSimpleName();
	}


}
