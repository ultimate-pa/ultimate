/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

/**
 * Collection of options specific to the usage of a {@link ParseEnvironment}.
 *
 * @author Juergen Christ
 */
public class FrontEndOptions {
	private final BooleanOption mPrintSuccess;
	private final ChannelOption mOut;
	private final BooleanOption mPrintTermsCSE;
	private final BooleanOption mContinueOnError;

	private static final String REG_OUT_CHANNEL_DEF = SMTLIBConstants.STDOUT;
	private static final String REG_OUT_CHANNEL_DESC =
			"Where to print command responses to.  Use \"stdout\" for standard "
					+ "output and \"stderr\" for standard error.";

	FrontEndOptions(final OptionMap options) {
		mPrintSuccess = (BooleanOption) options.getOption(":print-success");
		final Option outChannel = options.getOption(SMTLIBConstants.REGULAR_OUTPUT_CHANNEL);
		if (outChannel instanceof ChannelOption) {
			mOut = (ChannelOption) outChannel;
		} else {
			/* Frontend is not active */
			mOut = null;
		}
		mPrintTermsCSE = (BooleanOption) options.getOption(SMTInterpolOptions.PRINT_TERMS_CSE);
		mContinueOnError = (BooleanOption) options.getOption(SMTInterpolOptions.CONTINUE_ON_ERROR);
	}

	FrontEndOptions(final OptionMap options, final boolean active) {
		mPrintSuccess = new BooleanOption(true, true, "Print \"success\" after "
				+ "successful command executions that would otherwise not " + "produce feedback.");
		mPrintTermsCSE = new BooleanOption(true, true, "Eliminate common subexpressions before printing terms.");
		mContinueOnError = new BooleanOption(true, true,
				"Continue on errors.  Corresponds to (set-info :error-behavior continued-execution).");
		options.addOption(SMTLIBConstants.PRINT_SUCCESS, mPrintSuccess);
		if (active) {
			mOut = new ChannelOption(REG_OUT_CHANNEL_DEF, true, REG_OUT_CHANNEL_DESC);
			options.addOption(SMTLIBConstants.REGULAR_OUTPUT_CHANNEL, mOut);
		} else {
			options.addOption(SMTLIBConstants.REGULAR_OUTPUT_CHANNEL,
					new StringOptionWithWarning(REG_OUT_CHANNEL_DEF, true, REG_OUT_CHANNEL_DESC,
							"Front End not active.  Option change will not have an effect!", options.getLogProxy()));
			mOut = null;
		}
		options.addOption(SMTInterpolOptions.PRINT_TERMS_CSE, mPrintTermsCSE);
		options.addOption(SMTInterpolOptions.CONTINUE_ON_ERROR, mContinueOnError);
	}

	public final boolean isFrontEndActive() {
		return mOut != null;
	}

	public final boolean isPrintSuccess() {
		return mPrintSuccess.getValue();
	}

	public PrintWriter getOutChannel() {
		return mOut.getChannel();
	}

	public final boolean isPrintTermsCSE() {
		return mPrintTermsCSE.getValue();
	}

	public final boolean continueOnError() {
		return mContinueOnError.getValue();
	}
}
