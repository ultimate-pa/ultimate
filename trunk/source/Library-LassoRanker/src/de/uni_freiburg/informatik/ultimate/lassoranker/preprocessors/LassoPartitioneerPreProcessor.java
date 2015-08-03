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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneerPreProcessor extends LassoPreProcessor {
	public static final String s_Description = "LassoPartitioneer";
	
	private final IUltimateServiceProvider m_Services;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	
	private final Script m_Script;
	
	
	
	public LassoPartitioneerPreProcessor(Script script, 
			IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		m_Services = services;
		m_Script = script;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
	}

	@Override
	public Collection<LassoUnderConstruction> process(
			LassoUnderConstruction lasso) throws TermException {
		LassoPartitioneer lp = new LassoPartitioneer(m_Services, m_FreshTermVariableConstructor, m_Script, lasso);
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
