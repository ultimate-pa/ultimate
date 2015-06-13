/*
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE ModelCheckerUtils Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;


import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * SimplifyDDA extended by support for timeouts.
 * @author Matthias Heizmann
 *
 */
public class SimplifyDDAWithTimeout extends SimplifyDDA {
	
	private IUltimateServiceProvider mServices;

	/**
	 * {@inheritDoc}
	 */
	public SimplifyDDAWithTimeout(Script script, IUltimateServiceProvider services) {
		this(script, true, services);
	}
	
	/**
	 * {@inheritDoc}
	 */
	public SimplifyDDAWithTimeout(final Script script, 
			boolean simplifyRepeatedly, IUltimateServiceProvider services) {
		super(script, simplifyRepeatedly);
		mServices = services;
	}

	@Override
	protected Redundancy getRedundancy(Term term) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(this.getClass());
		}
		return super.getRedundancy(term);
	}
}
