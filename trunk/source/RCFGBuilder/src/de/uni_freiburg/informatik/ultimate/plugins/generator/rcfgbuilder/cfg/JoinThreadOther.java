/*
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class JoinThreadOther extends CodeBlock implements IIcfgJoinTransitionThreadOther<IcfgLocation> {

	private static final long serialVersionUID = 6045590312545516354L;

	protected JoinStatement mJoinStatement;
	protected JoinThreadCurrent mJoinCurrentThread;
	protected String mPrettyPrintedStatements;

	JoinThreadOther(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final JoinStatement st, final JoinThreadCurrent corresponsingCurrentJoin, final ILogger logger) {
		super(serialNumber, source, target, logger);
		mJoinStatement = st;
		mJoinCurrentThread = corresponsingCurrentJoin;
		mPrettyPrintedStatements = BoogiePrettyPrinter.print(st);
	}

	@Visualizable
	public JoinStatement getJoinStatement() {
		return mJoinStatement;
	}

	@Override
	public String getPrettyPrintedStatements() {
		return mPrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return mPrettyPrintedStatements;
	}

	@Override
	public UnmodifiableTransFormula getAssignmentOfJoin() {
		return getTransformula();
	}

	@Override
	public JoinThreadCurrent getCorrespondingIIcfgJoinTransitionCurrentThread() {
		return mJoinCurrentThread;
	}
}
