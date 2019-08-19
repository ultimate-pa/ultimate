/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Closeable;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Superclass to TerminationArgumentSynthesizer and NonTerminationArgumentSynthesizer.
 *
 * Contains some shared code.
 *
 * @author Jan Leike
 * @see TerminationArgumentSynthesizer
 * @see NonTerminationArgumentSynthesizer
 */
public abstract class ArgumentSynthesizer implements Closeable {
	protected final ILogger mLogger;

	/**
	 * Auxiliary String that we put into the smt script via an echo. This String should help to identify the difficult
	 * constraints in a bunch of dumped smt2 files.
	 */
	public final static String s_SolverUnknownMessage = "Warning solver responded UNKNOWN to the check-sat above";

	/**
	 * The SMT script for argument synthesis
	 */
	protected final Script mScript;

	/**
	 * The lasso program that we are analyzing
	 */
	protected final Lasso mLasso;

	/**
	 * Preferences
	 */
	protected final ILassoRankerPreferences mPreferences;

	/**
	 * Whether synthesize() has been called
	 */
	private boolean mSynthesisSuccessful = false;

	/**
	 * Whether close() has been called
	 */
	private boolean mClosed = false;

	protected IUltimateServiceProvider mServices;

	/**
	 * Constructor for the argument synthesizer
	 *
	 * @param lasso
	 *            the lasso program
	 * @param preferences
	 *            the preferences
	 * @param constaintsName
	 *            name of the constraints whose satisfiability is checked
	 * @throws IOException
	 */
	public ArgumentSynthesizer(final Lasso lasso, final ILassoRankerPreferences preferences,
			final String constaintsName, final IUltimateServiceProvider services) throws IOException {
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mPreferences = preferences;
		mLasso = lasso;
		mServices = services;
		mScript = constructScript(mPreferences, constaintsName);
	}

	/**
	 * @param constaintsName
	 *            Identifier for this script.
	 * @return SMT script that will be used for the argument synthesis
	 */
	protected abstract Script constructScript(ILassoRankerPreferences preferences, String constaintsName);

	/**
	 * @return the SMT script to be used for the argument synthesis
	 */
	public Script getScript() {
		return mScript;
	}

	/**
	 * @return whether the last call to synthesize() was successfull
	 */
	public boolean synthesisSuccessful() {
		return mSynthesisSuccessful;
	}

	/**
	 * Try to synthesize an argument for (non-)termination
	 *
	 * @return result of the solver while checking the constraints
	 * @throws IOException
	 */
	public final LBool synthesize() throws SMTLIBException, TermException, IOException {
		final LBool lBool = do_synthesis();
		mSynthesisSuccessful = (lBool == LBool.SAT);
		return lBool;
	}

	/**
	 * Try to synthesize an argument for (non-)termination This is to be derived in the child classes and is wrapped by
	 * synthesize().
	 *
	 * @return result of the solver while checking the constraints
	 * @throws IOException
	 */
	protected abstract LBool do_synthesis() throws SMTLIBException, TermException, IOException;

	/**
	 * Define a new constant
	 *
	 * @param name
	 *            name of the new constant
	 * @param sort
	 *            the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException
	 *             if something goes wrong, e.g. the name is already defined
	 */
	public Term newConstant(final String name, final String sortname) throws SMTLIBException {
		return SmtUtils.buildNewConstant(mScript, name, sortname);
	}

	/**
	 * Perform cleanup actions
	 */
	@Override
	public void close() {
		if (!mClosed) {
			mScript.exit();
			mClosed = true;
		}
	}

	@Override
	protected void finalize() throws Throwable {
		// Finalize methods are discouraged in Java.
		// Always call close() as exported by the Closable interface!
		// This is just a fallback to make sure close() has been called.
		close();
		super.finalize();
	}
}
