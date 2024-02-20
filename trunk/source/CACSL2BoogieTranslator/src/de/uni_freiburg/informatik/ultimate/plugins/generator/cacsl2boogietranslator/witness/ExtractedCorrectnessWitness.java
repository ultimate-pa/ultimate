/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Stores the information extracted from a correctness witness (commonly used for GraphML- and YAML-witnesses)
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedCorrectnessWitness {
	private final HashRelation<IASTNode, ExtractedWitnessInvariant> mInvariants = new HashRelation<>();
	private final HashRelation<IASTNode, ExtractedGhostUpdate> mGhostUpdates = new HashRelation<>();
	private final HashRelation<IASTNode, ExtractedFunctionContract> mFunctionContracts = new HashRelation<>();
	private final Set<IExtractedWitnessDeclaration> mGlobalDeclarations = new HashSet<>();

	public void addInvariant(final IASTNode node, final ExtractedWitnessInvariant invariant) {
		mInvariants.addPair(node, invariant);
	}

	public void addInvariants(final Map<IASTNode, ? extends ExtractedWitnessInvariant> map) {
		map.forEach(this::addInvariant);
	}

	public void addGhostUpdate(final IASTNode node, final ExtractedGhostUpdate update) {
		mGhostUpdates.addPair(node, update);
	}

	public void addFunctionContract(final IASTNode function, final ExtractedFunctionContract contract) {
		mFunctionContracts.addPair(function, contract);
	}

	public void addGlobalDeclaration(final IExtractedWitnessDeclaration decl) {
		mGlobalDeclarations.add(decl);
	}

	public List<IExtractedWitnessEntry> getWitnessStatements(final IASTNode node) {
		// Ensure that invariants are evaluated before the ghost variables are updated
		return Stream.concat(mGhostUpdates.getImage(node).stream(), mInvariants.getImage(node).stream())
				.collect(Collectors.toList());
	}

	public Set<ExtractedFunctionContract> getFunctionContracts(final IASTNode node) {
		return mFunctionContracts.getImage(node);
	}

	public Set<IExtractedWitnessDeclaration> getGlobalDeclarations() {
		return mGlobalDeclarations;
	}

	public void printWitness(final Consumer<String> printer) {
		if (mInvariants.isEmpty() && mFunctionContracts.isEmpty() && mGlobalDeclarations.isEmpty()
				&& mGhostUpdates.isEmpty()) {
			printer.accept("Witness did not contain any usable entries.");
			return;
		}
		printer.accept("Found the following entries in the witness:");
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entry : mInvariants.getSetOfPairs()) {
			printer.accept(entry.getValue().toString());
		}
		for (final Entry<IASTNode, ExtractedFunctionContract> entry : mFunctionContracts.getSetOfPairs()) {
			printer.accept(entry.getValue().toString());
		}
		for (final var d : mGlobalDeclarations) {
			printer.accept(d.toString());
		}
		for (final var entry : mGhostUpdates.getSetOfPairs()) {
			printer.accept(entry.getValue().toString());
		}
	}
}
