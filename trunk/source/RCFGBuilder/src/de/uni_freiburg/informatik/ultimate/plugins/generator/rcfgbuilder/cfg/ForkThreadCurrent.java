/*
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Edge in a recursive control flow graph that represents a fork call. Opposed to a Summary this represents only
 * the execution from the position directly before the fork statement to the next position of the current thread. A
 * ForkCurrentThread object provides one auxiliary TransitionFormula which shows fork th_id_X, where X is the number
 * of the created thread.
 *
 * @author lars.nitzke@outlook.com
 */
public class ForkThreadCurrent extends CodeBlock implements IIcfgForkTransitionThreadCurrent<IcfgLocation> {

	private static final long serialVersionUID = -2032583850030703623L;
	protected ForkStatement mForkStatement;
	protected String mPrettyPrintedStatements;

	@Visualizable
	private final boolean mForkedProcedureHasImplementation;

	private ForkSmtArguments mForkSmtArguments;


	ForkThreadCurrent(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final ForkStatement st, final boolean forkedProcedureHasImplementation, final ILogger logger) {
		super(serialNumber, source, target, logger);
		mForkStatement = st;
		mForkedProcedureHasImplementation = forkedProcedureHasImplementation;
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
	public ForkSmtArguments getForkSmtArguments() {
		return mForkSmtArguments;
	}

	public void setForkSmtArguments(final ForkSmtArguments forkSmtArguments) {
		mForkSmtArguments = forkSmtArguments;
	}

	@Override
	public String getNameOfForkedProcedure() {
		return mForkStatement.getProcedureName();
	}


}
