/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE ProofsTest Library.
 *
 * The ULTIMATE ProofsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ProofsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ProofsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ProofsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ProofsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OwickiGriesParser<L, P> {
	private static final String GHOST_VARIABLES_KEY = "ghost_variables";
	private static final String GHOST_UPDATES_KEY = "ghost_updates";
	private static final String ANNOTATIONS_KEY = "omega";

	private final Function<String, P> mParsePlaceName;
	private final BiFunction<Set<IProgramVar>, String, IPredicate> mParsePredicate;

	public OwickiGriesParser(final Function<String, P> parsePlaceName,
			final BiFunction<Set<IProgramVar>, String, IPredicate> parsePredicate) {
		mParsePlaceName = parsePlaceName;
		mParsePredicate = parsePredicate;
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> parse(final IPetriNet<L, P> program,
			final IIcfgSymbolTable programSymbolTable, final Set<String> procedures,
			final ThreadModularPrePostSpecification<P, Marking<P>> spec,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences, final Path yamlFile)
			throws IOException {
		try (var stream = new FileInputStream(yamlFile.toFile())) {
			final Map<String, Object> mapping = new Yaml().load(stream);

			final Map<IProgramVar, Term> ghostVariables = parseGhostVariableDeclarations(mapping);
			final Map<Transition<L, P>, GhostUpdate> ghostUpdates = parseGhostUpdates(program, mapping);
			final Map<P, IPredicate> annotations = parsePlaceAnnotations(program, ghostVariables.keySet(), mapping);

			final var annotationSymbolTable = new DefaultIcfgSymbolTable(programSymbolTable, procedures);
			for (final var ghost : ghostVariables.keySet()) {
				annotationSymbolTable.add(ghost);
			}

			return new OwickiGriesAnnotation<>(spec, possibleInterferences, annotationSymbolTable, annotations,
					ghostVariables.keySet(), ghostVariables, ghostUpdates);
		}
	}

	private Map<IProgramVar, Term> parseGhostVariableDeclarations(final Map<String, Object> mapping) {
		final var ghostVariableDeclarations = (List) mapping.get(GHOST_VARIABLES_KEY);
		if (ghostVariableDeclarations == null || ghostVariableDeclarations.isEmpty()) {
			return Map.of();
		}
		// TODO Parse ghost variables
		throw new UnsupportedOperationException("Parsing of ghost variables not yet implemented");
	}

	private Map<Transition<L, P>, GhostUpdate> parseGhostUpdates(final IPetriNet<L, P> program,
			final Map<String, Object> mapping) {
		final var ghostUpdates = (Map) mapping.get(GHOST_UPDATES_KEY);
		if (ghostUpdates == null || ghostUpdates.isEmpty()) {
			return Map.of();
		}
		// TODO Parse ghost variables
		throw new UnsupportedOperationException("Parsing of ghost updates not yet implemented");
	}

	private Map<P, IPredicate> parsePlaceAnnotations(final IPetriNet<L, P> program,
			final Set<IProgramVar> ghostVariables, final Map<String, Object> mapping) {
		if (!mapping.containsKey(ANNOTATIONS_KEY)) {
			throw new IllegalArgumentException("Owicki-Gries annotation must map places to formulas");
		}

		final var annotationsMap = (Map<String, Object>) mapping.get(ANNOTATIONS_KEY);
		final var result = new HashMap<P, IPredicate>();
		for (final var entry : annotationsMap.entrySet()) {
			final P place = mParsePlaceName.apply(entry.getKey());
			if (!program.getPlaces().contains(place)) {
				throw new IllegalArgumentException(
						"Place %s (syntax: %s) is not in the program".formatted(place, entry.getKey()));
			}

			// Handle booleans, such that true and false need not be quoted in YAML
			final String formulaString =
					entry.getValue() instanceof final Boolean b ? Boolean.toString(b) : (String) entry.getValue();
			final IPredicate formula = mParsePredicate.apply(ghostVariables, formulaString);
			result.put(place, formula);
		}

		return result;
	}
}
