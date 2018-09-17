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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Edge in a recursive control flow graph that represents a fork call. Opposed to a Summary this represents only
 * the execution from the position directly before the fork statement to the initial position of the forked procedure. A
 * ForkOtherThread object provides three auxiliary TransitionFormulas. Two of them assign the global variables th_id_X
 * and th_X_inUse. The other one shows the actual fork statement of the code.
 *
 * @author lars.nitzke@outlook.com
 */
public class ForkThreadOther extends CodeBlock implements IIcfgForkTransitionThreadOther<IcfgLocation> {

	private static final long serialVersionUID = 5866537291870187570L;
	protected ForkStatement mForkStatement;
	protected ForkThreadCurrent mForkCurrentThread;
	protected String mPrettyPrintedStatements;

	ForkThreadOther(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final ForkStatement st, final ForkThreadCurrent forkCurrentThread, final ILogger logger) {
		super(serialNumber, source, target, logger);
		mForkStatement = st;
		mForkCurrentThread = forkCurrentThread;
		mPrettyPrintedStatements = BoogiePrettyPrinter.print(st);
	}

	@Visualizable
	public ForkStatement getForkStatement() {
		return mForkStatement;
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
	public UnmodifiableTransFormula getLocalVarsAssignment() {
		return getTransformula();
	}

	@Override
	public ForkThreadCurrent getCorrespondingIIcfgForkTransitionCurrentThread() {
		return mForkCurrentThread;
	}
}
