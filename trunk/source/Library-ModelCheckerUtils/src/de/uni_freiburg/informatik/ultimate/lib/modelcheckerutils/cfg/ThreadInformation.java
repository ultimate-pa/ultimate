package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ThreadInformation<LETTER extends IIcfgTransition<?>> {
	private final Map<String, List<String>> mTemplates2Instances;
	private final Map<String, Map<TermVariable, TermVariable>> mTemplateVars2InstanceVars;
	private final Map<String, List<IcfgEdge>> mInstances2Forks;
	private final Map<String, IcfgLocation> mEntryNodes;
	private final Map<String, List<IcfgEdge>> mThreads2Actions;

	public ThreadInformation(final IIcfg<IcfgLocation> icfg) {
		final var toolkit = icfg.getCfgSmtToolkit();
		mEntryNodes = icfg.getProcedureEntryNodes();
		final var symbolTable = toolkit.getSymbolTable();
		mTemplates2Instances = new HashMap<>();
		mTemplateVars2InstanceVars = new HashMap<>();
		mInstances2Forks = new HashMap<>();
		mThreads2Actions = new HashMap<>();
		for (final var threads : toolkit.getConcurrencyInformation().getThreadInstanceMap().values()) {
			for (final var t : threads) {
				final String instance = t.getThreadInstanceName();
				final String template = t.getThreadTemplateName();
				mInstances2Forks.put(instance, mEntryNodes.get(instance).getIncomingEdges());
				var instances = mTemplates2Instances.get(template);
				if (instances == null) {
					instances = new ArrayList<>();
					mTemplates2Instances.put(template, instances);
				}
				instances.add(instance);
				final Map<String, TermVariable> identifier2TemplateVar = symbolTable.getLocals(template).stream()
						.collect(Collectors.toMap(x -> x.getIdentifier(), x -> x.getTermVariable()));
				mTemplateVars2InstanceVars.put(instance, symbolTable.getLocals(instance).stream().collect(Collectors
						.toMap(x -> identifier2TemplateVar.get(x.getIdentifier()), x -> x.getTermVariable())));
			}
		}
		mTemplates2Instances.values().forEach(Collections::sort);
	}

	public Substitution getTermSubstitution(final ThreadInformation<LETTER> newThreadInfo,
			final Map<String, String> new2OldInstances, final Script script) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final var entry : new2OldInstances.entrySet()) {
			final var newVarMap = newThreadInfo.mTemplateVars2InstanceVars.get(entry.getKey());
			final var oldVarMap = mTemplateVars2InstanceVars.get(entry.getValue());
			oldVarMap.keySet().forEach(x -> substitution.put(oldVarMap.get(x), newVarMap.get(x)));
		}
		return new Substitution(script, substitution);
	}

	public List<Map<String, String>> getThreadInstanceSubstitutions(final ThreadInformation<LETTER> newThreadInfo) {
		final List<Map<String, String>> addedThreadMappings = new ArrayList<>();
		final BidirectionalMap<String, String> identityMapping = new BidirectionalMap<>();
		for (final String template : mTemplates2Instances.keySet()) {
			final List<String> oldInstances = mTemplates2Instances.get(template);
			final List<String> newInstances = newThreadInfo.mTemplates2Instances.get(template);
			for (int i = 0; i < oldInstances.size(); i++) {
				identityMapping.put(newInstances.get(i), oldInstances.get(i));
			}
			if (newInstances.size() > oldInstances.size()) {
				// TODO: Could we generalize this?
				assert newInstances.size() == oldInstances.size() + 1;
				assert addedThreadMappings.isEmpty();
				final String addedInstance = newInstances.get(oldInstances.size());
				for (int j = 0; j < oldInstances.size(); j++) {
					addedThreadMappings.add(Collections.singletonMap(addedInstance, oldInstances.get(j)));
				}
			}
		}
		final List<Map<String, String>> result = new ArrayList<>(addedThreadMappings.size() + 1);
		result.add(identityMapping);
		for (final var map : addedThreadMappings) {
			final Map<String, String> resultMap = new BidirectionalMap<>(identityMapping);
			map.forEach(resultMap::put);
			result.add(resultMap);
		}
		return result;
	}

	public List<IcfgEdge> getActions(final String thread) {
		List<IcfgEdge> result = mThreads2Actions.get(thread);
		if (result == null) {
			// TODO: What happens, if we have multiple incoming edges (i.e. forks)?
			final var iterator = new IcfgEdgeIterator(mEntryNodes.get(thread).getIncomingEdges());
			result = iterator.asStream().collect(Collectors.toList());
			mThreads2Actions.put(thread, result);
		}
		return result;
	}
}
