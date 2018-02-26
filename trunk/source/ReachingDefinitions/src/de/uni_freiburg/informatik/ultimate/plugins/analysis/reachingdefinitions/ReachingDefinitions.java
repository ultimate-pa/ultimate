/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefGraphAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefMapAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.AssumeFinder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg.ParallelDfgGeneratorObserver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.preferences.ReachingDefinitionsPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.rcfg.ReachDefRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace.ReachDefTrace;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ReachingDefinitions implements IAnalysis {
	
	private ModelType mCurrentGraphType;
	private IUltimateServiceProvider mServices;
	
	@Override
	public ModelType getOutputDefinition() {
		return mCurrentGraphType;
	}
	
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	
	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}
	
	@Override
	public List<String> getDesiredToolIds() {
		return null;
	}
	
	@Override
	public void setInputDefinition(final ModelType graphType) {
		mCurrentGraphType = graphType;
	}
	
	@Override
	public List<IObserver> getObservers() {
		if (mCurrentGraphType.getCreator()
				.equals(de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator.PLUGIN_ID)) {
			final IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider =
					new ReachDefGraphAnnotationProvider<>(null);
			final IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider =
					new ReachDefGraphAnnotationProvider<>(null);
			final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
			
			final AssumeFinder finder = new AssumeFinder(logger);
			
			final List<IObserver> rtr = new ArrayList<>();
			rtr.add(new ReachDefRCFG(logger, stmtProvider, edgeProvider));
			rtr.add(finder);
			// rtr.add(new DataflowDAGGenerator(logger, stmtProvider,
			// edgeProvider, finder.getEdgesWithAssumes()));
			
			if (mServices.getPreferenceProvider(getPluginID())
					.getBoolean(ReachingDefinitionsPreferenceInitializer.LABEL_COMPUTE_PARRALLEL_DFG)) {
				rtr.add(new ParallelDfgGeneratorObserver(logger, mServices));
			}
			
			return rtr;
		}
		return Collections.emptyList();
	}
	
	@Override
	public void init() {
	}
	
	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}
	
	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}
	
	@Override
	public IPreferenceInitializer getPreferences() {
		return new ReachingDefinitionsPreferenceInitializer();
	}
	
	public static List<DataflowDAG<TraceCodeBlock>> computeRDForTrace(final List<CodeBlock> trace, final ILogger logger,
			final IElement rootNode) throws Throwable {
		return computeRDForTrace(trace, logger, PreprocessorAnnotation.getAnnotation(rootNode).getSymbolTable());
	}
	
	public static List<DataflowDAG<TraceCodeBlock>> computeRDForTrace(final List<CodeBlock> trace, final ILogger logger,
			final BoogieSymbolTable symbolTable) throws Throwable {
		final IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider = new ReachDefMapAnnotationProvider<>();
		final IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider = new ReachDefMapAnnotationProvider<>();
		final ReachDefTrace rdt = new ReachDefTrace(edgeProvider, stmtProvider, logger, symbolTable);
		return rdt.process(trace);
	}
	
	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		
	}
	
	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
	}
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
	
}
