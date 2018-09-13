/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CTranslationResultReporter {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final boolean mReportUnsoundnessWarning;

	public CTranslationResultReporter(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mLogger = logger;

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mReportUnsoundnessWarning = prefs.getBoolean(CACSLPreferenceInitializer.LABEL_REPORT_UNSOUNDNESS_WARNING);
	}

	/**
	 * Report possible source of unsoundness to Ultimate.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param longDesc
	 *            description.
	 */
	public void warn(final ILocation loc, final String longDescription) {
		if (!mReportUnsoundnessWarning) {
			return;
		}

		final String shortDescription = "Unsoundness Warning";
		mLogger.warn(shortDescription + " " + longDescription);
		final GenericResultAtLocation result = new GenericResultAtLocation(Activator.PLUGIN_NAME, loc, shortDescription,
				longDescription, Severity.WARNING);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	/**
	 * Report a syntax error to Ultimate. This will cancel the toolchain.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param type
	 *            why did it happen?
	 * @param msg
	 *            description.
	 */
	public void syntaxError(final ILocation loc, final String msg) {
		final SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME, loc, msg);
		mLogger.warn(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	/**
	 * Report a unsupported syntax to Ultimate. This will cancel the toolchain.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param type
	 *            why did it happen?
	 * @param msg
	 *            description.
	 */
	public void unsupportedSyntax(final ILocation loc, final String msg) {
		final UnsupportedSyntaxResult<IElement> result = new UnsupportedSyntaxResult<>(Activator.PLUGIN_NAME, loc, msg);
		mLogger.warn(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

}
