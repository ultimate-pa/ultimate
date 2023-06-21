/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de) 
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ChcEvidenceExtractor plug-in.
 *
 * The ULTIMATE ChcEvidenceExtractor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ChcEvidenceExtractor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ChcEvidenceExtractor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ChcEvidenceExtractor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ChcEvidenceExtractor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chcevidenceextractor;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcSolution;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot.IChcBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.chc.ProgramAnnot;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ChcEvidenceExtractorObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<?> mModel;

	public ChcEvidenceExtractorObserver(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mLogger = logger;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof ChcSolution)) {
			return true;
		}

		final ChcSolution chcSolution = (ChcSolution) root;
		if (chcSolution.getSatisfiability() != LBool.SAT) {
			// TODO: We should report unknown here
			return false;
		}
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new AllSpecificationsHoldResult(Activator.PLUGIN_ID, ""));
		final Model model = chcSolution.getModel();
		if (model == null) {
			return false;
		}
		final IChcBacktranslator backtranslator = chcSolution.getBacktranslator();
		if (backtranslator == null) {
			throw new UnsupportedOperationException("Solution does not contain a backtranslator");
		}
		final ProgramAnnot programAnnot = backtranslator.backtranslate(model);
		final Map<List<IcfgLocation>, Term> map = programAnnot.toProductMap((progVar, instance) -> {
			if (instance == 0) {
				return progVar.getTermVariable();
			}
			throw new UnsupportedOperationException("Local variables for multiple threads are not supported yet.");
		}, backtranslator.getIcfg().getCfgSmtToolkit().getManagedScript());
		for (final Entry<List<IcfgLocation>, Term> entry : map.entrySet()) {
			mLogger.info("Invariant at " + entry);
		}
		// TODO: Annotate the icfg?
		mModel = backtranslator.getIcfg();

		return false;
	}

	public IElement getModel() {
		return mModel;
	}
}
