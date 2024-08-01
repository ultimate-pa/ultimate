/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.btortranslator;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.btorutils.BtorScript;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class CfgToBtorObserver extends BaseObserver {
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private IElement mResult;

	public CfgToBtorObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	public IElement getModel() {
		return mResult;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg) {
			processIcfg((IIcfg<IcfgLocation>) root);
			return false;
		}
		return true;
	}

	private void processIcfg(final IIcfg<IcfgLocation> icfg) {
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final CFGToBTOR processor = new CFGToBTOR(mgdScript, mServices);
		processor.extractLocations(icfg);
		processor.extractVariables(icfg);
		processor.extractTransitions(icfg);
		processor.extractBadStates(icfg);
		final BtorScript script = processor.generateScript(icfg);
		try {
			script.dumpScript(new OutputStreamWriter(System.out)); //
			final File btorFile = File.createTempFile("prefix", ".btor2");
			final FileOutputStream btorFileStream = new FileOutputStream(btorFile);
			script.dumpScript(new OutputStreamWriter(btorFileStream));

			System.out.println(btorFile.getAbsolutePath());

			final ProcessBuilder processBuilder = new ProcessBuilder();
			processBuilder.command("/usr/local/bin/btormc", "--trace-gen-full", btorFile.getAbsolutePath());

			final Process process = processBuilder.start();
			final StringBuilder btormcOutput = new StringBuilder();
			final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			final int exitVal = process.waitFor();
			String line;
			while ((line = reader.readLine()) != null) {
				btormcOutput.append(line + "\n");
			}
			final String btormcWitness = btormcOutput.toString();
			System.out.println(btormcWitness.toString());
			System.out.println(exitVal);

			final IIcfgElement rootLocation = icfg.getInitialNodes().iterator().next();

			if (btormcWitness.startsWith("sat")) {
				final ArrayList<Integer> pcList = new ArrayList<>();
				final Map<Integer, Map<String, Integer>> programStateSequence = new HashMap<>();
				final Pattern p = Pattern.compile("([01]{64}) ([a-zA-Z][a-zA-Z0-9_]*)#(\\d+)");
				final Matcher m = p.matcher(btormcWitness);
				while (m.find()) {
					if (m.group(2).equals("pc")) {
						pcList.add(Integer.parseInt(m.group(1), 2));
					} else {
						final int sequenceNumber = Integer.parseInt(m.group(3));
						if (!programStateSequence.containsKey(sequenceNumber)) {
							programStateSequence.put(sequenceNumber, new HashMap<>());
						}
						programStateSequence.get(sequenceNumber).put(m.group(2), Integer.parseInt(m.group(1), 2));

					}
				}
				System.out.println(pcList);
				System.out.println(programStateSequence);
				final IcfgProgramExecution<IcfgEdge> pe =
						processor.extractErrorTrace(icfg, pcList, programStateSequence);
				final CounterExampleResult nResult = new CounterExampleResult<>(rootLocation, Activator.PLUGIN_ID,
						mServices.getBacktranslationService(), pe);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, nResult);
			} else {
				final PositiveResult<IIcfgElement> pResult = new PositiveResult<IIcfgElement>(Activator.PLUGIN_ID,
						rootLocation, mServices.getBacktranslationService());
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, pResult);
			}

		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (final InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
