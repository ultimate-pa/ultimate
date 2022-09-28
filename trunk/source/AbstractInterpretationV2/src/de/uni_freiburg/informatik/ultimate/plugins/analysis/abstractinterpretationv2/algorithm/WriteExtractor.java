package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class WriteExtractor<ACTION extends IIcfgTransition<?>> {
	private final HashRelation<IProgramVar, String> mWritesToProcedures;
	private final HashRelation<IProgramVar, String> mReadsToProcedures;

	private final HashRelation<ACTION, IProgramVar> mWritesToSharedVariables;

	public WriteExtractor(final IIcfg<?> icfg) {
		final HashRelation<ACTION, IProgramVar> writesToVariables = new HashRelation<>();
		mWritesToProcedures = new HashRelation<>();
		mReadsToProcedures = new HashRelation<>();
		mWritesToSharedVariables = new HashRelation<>();
		for (final Entry<String, ?> entry : icfg.getProcedureEntryNodes().entrySet()) {
			final String procedure = entry.getKey();
			final List<IcfgEdge> initalEdges = ((IcfgLocation) entry.getValue()).getOutgoingEdges();
			new IcfgEdgeIterator(initalEdges).forEachRemaining(edge -> {
				final TransFormula transformula = edge.getTransformula();
				final Set<IProgramVar> writtenVars = transformula.getAssignedVars();
				writesToVariables.addAllPairs((ACTION) edge, writtenVars);
				writtenVars.forEach(x -> mWritesToProcedures.addPair(x, procedure));
				transformula.getInVars().forEach((k, v) -> mReadsToProcedures.addPair(k, procedure));
			});
		}
		final Set<IProgramVar> sharedVars =
				mReadsToProcedures.getDomain().stream().filter(this::isSharedVariable).collect(Collectors.toSet());
		for (final Entry<ACTION, HashSet<IProgramVar>> entry : writesToVariables.entrySet()) {
			final Set<IProgramVar> writtenSharedVars = DataStructureUtils.intersection(entry.getValue(), sharedVars);
			if (!writtenSharedVars.isEmpty()) {
				mWritesToSharedVariables.addAllPairs(entry.getKey(), writtenSharedVars);
			}
		}
	}

	private boolean isSharedVariable(final IProgramVar var) {
		final Set<String> writingProcedures = mWritesToProcedures.getImage(var);
		if (writingProcedures.isEmpty()) {
			return false;
		}
		final Set<String> readingProcedures = mReadsToProcedures.getImage(var);
		if (readingProcedures.isEmpty()) {
			return false;
		}
		if (writingProcedures.size() > 1 || readingProcedures.size() > 1) {
			return true;
		}
		// readingProcedures and writingProcedures are both singleton, return true iff they are different
		return !readingProcedures.equals(writingProcedures);
	}

	public HashRelation<ACTION, IProgramVar> getWritesToSharedVariables() {
		return mWritesToSharedVariables;
	}
}
