/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtParser plug-in.
 *
 * The ULTIMATE SmtParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.smtparser;

import de.uni_freiburg.informatik.ultimate.core.lib.results.MSODResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 * @author Daniel Dietsch
 */
public class ResultReportingWrapperScript extends WrapperScript {
	private final IUltimateServiceProvider mServices;

	public ResultReportingWrapperScript(final Script wrappedScript, final IUltimateServiceProvider services) {
		super(wrappedScript);
		mServices = services;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final LBool result = super.checkSat();

		switch (result) {
		case SAT:
			// TODO: mServices.getResultService().reportResult(pluginId, result);
			break;
		case UNKNOWN:
			break;
		case UNSAT:
			break;
		default:
			throw new UnsupportedOperationException("Unknown case: " + result);
		}

		final IResult msodResult = new MSODResult(Activator.PLUGIN_ID, "MSODResult",
				"MSOD resulted in: " + result.toString(), result, Severity.INFO);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, msodResult);

		return result;
	}
}