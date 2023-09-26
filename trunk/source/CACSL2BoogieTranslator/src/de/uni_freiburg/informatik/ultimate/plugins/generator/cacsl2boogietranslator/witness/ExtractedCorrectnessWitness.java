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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Stores the information extracted from a correctness witness (commonly used for GraphML- and YAML-witnesses)
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedCorrectnessWitness {
	private final HashRelation<IASTNode, IExtractedWitnessEntry> mWitnessStatements = new HashRelation<>();
	private final HashRelation<IASTNode, ExtractedFunctionContract> mFunctionContracts = new HashRelation<>();
	private final Set<IExtractedWitnessDeclaration> mGlobalDeclarations = new HashSet<>();

	public void addWitnessStatement(final IASTNode node, final IExtractedWitnessEntry entry) {
		mWitnessStatements.addPair(node, entry);
	}

	public void addWitnessStatements(final Map<IASTNode, ? extends IExtractedWitnessEntry> map) {
		map.forEach(this::addWitnessStatement);
	}

	public void addFunctionContract(final IASTNode function, final ExtractedFunctionContract contract) {
		mFunctionContracts.addPair(function, contract);
	}

	public void addGlobalDeclaration(final IExtractedWitnessDeclaration decl) {
		mGlobalDeclarations.add(decl);
	}

	public Set<IExtractedWitnessEntry> getWitnessStatements(final IASTNode node) {
		return mWitnessStatements.getImage(node);
	}

	public Set<ExtractedFunctionContract> getFunctionContracts(final IASTNode node) {
		return mFunctionContracts.getImage(node);
	}

	public Set<IExtractedWitnessDeclaration> getGlobalDeclarations() {
		return mGlobalDeclarations;
	}

	public void printWitness(final Consumer<String> printer) {
		if (mWitnessStatements.isEmpty() && mFunctionContracts.isEmpty() && mGlobalDeclarations.isEmpty()) {
			printer.accept("Witness did not contain any usable entries.");
			return;
		}
		printer.accept("Found the following entries in the witness:");
		for (final Entry<IASTNode, IExtractedWitnessEntry> entry : mWitnessStatements.getSetOfPairs()) {
			printer.accept(entry.getValue().toString());
		}
		for (final Entry<IASTNode, ExtractedFunctionContract> entry : mFunctionContracts.getSetOfPairs()) {
			printer.accept(entry.getValue().toString());
		}
		for (final var d : mGlobalDeclarations) {
			printer.accept(d.toString());
		}
	}
}
