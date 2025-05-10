/*
 * Copyright (C) 2025 Xinyu Jiang (xinyu.jiang@saturn.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CfgToBtor plug-in.
 *
 * The ULTIMATE CfgToBtor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CfgToBtor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CfgToBtor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CfgToBtor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CfgToBtor plug-in grant you additional permission
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
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.btorutils.BtorScript;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 *
 * @author Xinyu Jiang (xinyu.jiang@saturn.uni-freiburg.de)
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
			processIcfg((IIcfg<BoogieIcfgLocation>) root);
			return false;
		}
		return true;
	}

	private void processIcfg(final IIcfg<BoogieIcfgLocation> icfg) throws Exception {
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		Boogie2SMT boogie2SMT = null;
		if (icfg instanceof BoogieIcfgContainer) {
			final BoogieIcfgContainer bIcfg = (BoogieIcfgContainer) icfg;
			boogie2SMT = bIcfg.getBoogie2SMT();
		}

		// Preprocess icfg by extracting relevant information.
		final CFGToBTOR processor = new CFGToBTOR(mgdScript, mServices, boogie2SMT);
		processor.extractLocations(icfg);
		processor.extractVariables(icfg);
		processor.extractTransitions(icfg);
		processor.extractBadStates(icfg);
		// Generate the BTOR script using extracted information.
		final BtorScript script = processor.generateScript(icfg);
		try {
			// Dump script to console and temp file.
			script.dumpScript(new OutputStreamWriter(System.out));
			final File btorFile = File.createTempFile("prefix", ".btor2");
			final FileOutputStream btorFileStream = new FileOutputStream(btorFile);
			script.dumpScript(new OutputStreamWriter(btorFileStream));

			System.out.println(btorFile.getAbsolutePath());

			// Build btormc process with given parameters.
			// TODO: (@xinyu) take parameters as inputs.
			final ProcessBuilder processBuilder = new ProcessBuilder();
			// Run k-induction with kmax of 50.
			processBuilder.command("/usr/local/bin/btormc", "--trace-gen-full", "--kind", "-kmax", "50",
					btorFile.getAbsolutePath());

			// Run btormc process with timeout and extract process output.
			// TODO: (@xinyu) take timeout as input.
			final Process process = processBuilder.start();
			final StringBuilder btormcOutput = new StringBuilder();
			final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			final boolean finished = process.waitFor(30, TimeUnit.SECONDS);
			String line;
			while (finished && (line = reader.readLine()) != null) {
				btormcOutput.append(line + "\n");
			}
			final String btormcWitness = btormcOutput.toString();
			System.out.println(btormcWitness.toString());
			if (finished) {
				System.out.println(process.exitValue());
			} else {
				System.out.println("timeout");

			}

			// Assume one initial node for trace generation.
			final IIcfgElement rootLocation = icfg.getInitialNodes().iterator().next();

			// If there are error locations, process btormc output.
			if (!icfg.getProcedureErrorNodes().values().isEmpty()) {
				// Get error nodes.
				final Set<BoogieIcfgLocation> errorLocations = icfg.getProcedureErrorNodes().values().iterator().next();
				if (!finished) {
					// Return timeout result if btormc did not return.
					final TimeoutResult timeoutResult =
							new TimeoutResult(Activator.PLUGIN_ID, "btormc timeout reached");
					mServices.getResultService().reportResult(Activator.PLUGIN_ID, timeoutResult);
				} else if (process.exitValue() != 0) {
					// Throw exception if btormc failed.
					throw new Exception("btormc returned nonzero exit value");
				} else if (btormcWitness.startsWith("sat")) {
					// Generate error trace if an error location is reachable.

					// Parse btormc witness into a sequence of program states.
					final ArrayList<Long> pcList = new ArrayList<>();
					final Map<Long, Map<String, Long>> programStateSequence = new HashMap<>();
					final Pattern p = Pattern.compile("([01]+) ([a-zA-Z][a-zA-Z0-9_]*)#(\\d+)");
					final Matcher m = p.matcher(btormcWitness);
					while (m.find()) {
						if (m.group(2).equals("pc")) {
							pcList.add(Long.parseLong(m.group(1), 2));
						} else {
							final long sequenceNumber = Long.parseUnsignedLong(m.group(3));
							if (!programStateSequence.containsKey(sequenceNumber)) {
								programStateSequence.put(sequenceNumber, new HashMap<>());
							}
							programStateSequence.get(sequenceNumber).put(m.group(2),
									Long.parseUnsignedLong(m.group(1), 2));

						}
					}
					System.out.println(pcList);
					System.out.println(programStateSequence);
					// Convert program state sequence into icfg program execution.
					final IcfgProgramExecution<IcfgEdge> pe =
							processor.extractErrorTrace(icfg, pcList, programStateSequence);
					// Send counterexample result to Ultimate backend.
					final CounterExampleResult<IcfgLocation, IcfgEdge, Term> nResult = new CounterExampleResult<>(
							pe.getTraceElement(pe.getLength() - 1).getTraceElement().getTarget(), Activator.PLUGIN_ID,
							mServices.getBacktranslationService(), pe);
					mServices.getResultService().reportResult(Activator.PLUGIN_ID, nResult);
				} else {
					// Error location is not reachable within the timeout limit.
					// TODO: (@xinyu) make this correct, send unknown result unless an unsat result is returned
					// TODO: (@xinyu) handle multiple sat results, or unsat followed by sat, etc etc
					mServices.getResultService().reportResult(Activator.PLUGIN_ID, AllSpecificationsHoldResult
							.createAllSpecificationsHoldResult(Activator.PLUGIN_ID, errorLocations.size()));
					for (final IcfgLocation errorLocation : errorLocations) {
						final PositiveResult<IIcfgElement> pResult = new PositiveResult<>(Activator.PLUGIN_ID,
								errorLocation, mServices.getBacktranslationService());
						mServices.getResultService().reportResult(Activator.PLUGIN_ID, pResult);
					}

				}

			}
			mServices.getResultService().reportResult(Activator.PLUGIN_ID,
					AllSpecificationsHoldResult.createAllSpecificationsHoldResult(Activator.PLUGIN_ID, 0));

		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (final InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
