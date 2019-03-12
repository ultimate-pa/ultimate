/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE LogicalInterpretation plug-in.
 *
 * The ULTIMATE LogicalInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LogicalInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LogicalInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LogicalInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LogicalInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.logicalinterpretation;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class LogicalInterpretationObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public LogicalInterpretationObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg<?>) {
			// TODO: Do something
			return false;
		}
		return true;
	}
}
