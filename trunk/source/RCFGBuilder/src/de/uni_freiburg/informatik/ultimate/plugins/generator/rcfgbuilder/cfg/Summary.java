/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Edge in a recursive control flow graph that represents the call of a procedure, including execution of the procedure,
 * returning to the caller and update of the left hand side of a call statement.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Summary extends CodeBlock implements IIcfgSummaryTransition<IcfgLocation> {

	private static final long serialVersionUID = 6048827510357561291L;

	private final CallStatement mCallStatement;
	private String mPrettyPrintedStatements;

	@Visualizable
	private final boolean mCalledProcedureHasImplementation;

	Summary(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final CallStatement st, final boolean calledProcedureHasImplementation, final ILogger logger) {
		super(serialNumber, source, target, logger);
		mCallStatement = st;
		mCalledProcedureHasImplementation = calledProcedureHasImplementation;
		mPrettyPrintedStatements = null;
	}

	@Override
	public boolean calledProcedureHasImplementation() {
		return mCalledProcedureHasImplementation;
	}

	@Visualizable
	public CallStatement getCallStatement() {
		return mCallStatement;
	}

	@Override
	public String getPrettyPrintedStatements() {
		if (mPrettyPrintedStatements == null) {
			mPrettyPrintedStatements = BoogiePrettyPrinter.print(mCallStatement);
		}
		return mPrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return "SUMMARY for " + getPrettyPrintedStatements() + " srcloc: " + mSource;
	}
}
