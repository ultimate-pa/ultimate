/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.EmpireAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EmpireAnnotationParser<P> {
	private static final Pattern QUOTED_PLACE_REGEX = Pattern.compile("\\s*\"((\\\"|[^\"])*)\".*");
	private static final Pattern IDENTIFIER_REGEX_NO_SUFFIX = Pattern.compile("\\s*([^\\s,\"\\}]*)(?=[\\s,\"\\}].*|$)");
	private static final Pattern IDENTIFIER_REGEX = Pattern.compile("\\s*([^\\s,\"\\}]*)([\\s,\"\\}].*|$)");
	private static final String PLACE_REGEX =
			"((" + QUOTED_PLACE_REGEX.pattern() + ")|(" + IDENTIFIER_REGEX_NO_SUFFIX.pattern() + "))";
	private static final Pattern REGION_LITERAL_REGEX =
			Pattern.compile("\\s*\\{(\\s*" + PLACE_REGEX + "\\s*(,\\s*" + PLACE_REGEX + "\\s*)*)\\}.*");

	private final Function<String, P> mParsePlaceName;
	private final Function<String, IPredicate> mParsePredicate;
	private final Function<List<IPredicate>, IPredicate> mConjunction;

	public EmpireAnnotationParser(final Function<String, P> parsePlaceName,
			final Function<String, IPredicate> parsePredicate,
			final Function<List<IPredicate>, IPredicate> conjunction) {
		mParsePlaceName = parsePlaceName;
		mParsePredicate = parsePredicate;
		mConjunction = conjunction;
	}

	public EmpireAnnotation<P> parse(final Stream<String> lines) {
		final Map<String, Region<P>> knownRegions = new HashMap<>();
		final Map<Territory<P>, List<IPredicate>> law = new HashMap<>();

		for (final var line : (Iterable<String>) lines::iterator) {
			// ignore blank lines and comments
			if (line.trim().startsWith("#") || line.isBlank()) {
				continue;
			}

			final Pair<String, Region<P>> regionDef;
			final Pair<Territory<P>, IPredicate> lawDef;

			if ((regionDef = parseRegionDefinition(line)) != null) {
				if (knownRegions.containsKey(regionDef.getFirst())) {
					throw new IllegalArgumentException("region name already used: " + regionDef.getFirst());
				}
				knownRegions.put(regionDef.getFirst(), regionDef.getSecond());
			} else if ((lawDef = parseLaw(line, knownRegions)) != null) {
				law.computeIfAbsent(lawDef.getFirst(), x -> new ArrayList<>()).add(lawDef.getSecond());
			} else {
				throw parseError("line", line);
			}
		}

		final var conjoinedLaw = law.entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> mConjunction.apply(e.getValue())));
		return new EmpireAnnotation<>(conjoinedLaw);
	}

	public P parsePlace(final String syntax) {
		final var result = parsePlaceInternal(syntax);
		if (result == null || result.getOffset() != syntax.length()) {
			throw parseError("place", syntax);
		}
		return result.getValue();
	}

	private Pair<String, Region<P>> parseRegionDefinition(final String syntaxLine) {
		final String trimmedSyntax = syntaxLine.trim();

		final String prefix = "region ";
		if (!trimmedSyntax.startsWith(prefix)) {
			return null;
		}

		final String definition = trimmedSyntax.substring(prefix.length());
		final var nameResult = parseIdentifierInternal(definition);
		if (nameResult == null) {
			throw parseError("region definition", syntaxLine);
		}

		final int colon = definition.indexOf(':', nameResult.getOffset());
		final String body = definition.substring(colon + 1);
		final var literalResult = parseRegionLiteralInternal(body);
		if (literalResult == null || literalResult.getOffset() != body.length()) {
			throw parseError("region definition", syntaxLine);
		}

		return new Pair<>(nameResult.getValue(), literalResult.getValue());
	}

	private Pair<Territory<P>, IPredicate> parseLaw(final String syntaxLine,
			final Map<String, Region<P>> knownRegions) {
		final String trimmedSyntax = syntaxLine.trim();

		final String prefix = "law ";
		if (!trimmedSyntax.startsWith(prefix)) {
			return null;
		}

		final String definition = trimmedSyntax.substring(prefix.length());
		final var territoryResult = parseTerritoryInternal(definition, knownRegions);

		final int colon = definition.indexOf(':', territoryResult.getOffset());
		final String body = definition.substring(colon + 1);
		final var predicate = mParsePredicate.apply(body);

		return new Pair<>(territoryResult.getValue(), predicate);
	}

	private Result<Territory<P>> parseTerritoryInternal(final String syntax,
			final Map<String, Region<P>> knownRegions) {
		final int opening = syntax.indexOf('{');
		if (opening < 0) {
			throw parseError("territory", syntax);
		}

		final Set<Region<P>> regions = new HashSet<>();
		String content = syntax.substring(opening + 1);
		int offset = opening + 1;

		int comma = -1;
		do {
			content = content.substring(comma + 1);
			offset += comma + 1;
			final var regionResult = parseRegionInternal(content, knownRegions);
			if (regionResult == null) {
				throw parseError("territory", syntax);
			}
			regions.add(regionResult.getValue());
			comma = content.indexOf(',', regionResult.getOffset());
		} while (comma > 0);

		offset += content.indexOf('}') + 1;
		return new Result<>(offset, new Territory<>(ImmutableSet.of(regions)));
	}

	private Result<Region<P>> parseRegionInternal(final String syntax, final Map<String, Region<P>> knownRegions) {
		final var literalResult = parseRegionLiteralInternal(syntax);
		if (literalResult != null) {
			return literalResult;
		}

		final var nameResult = parseIdentifierInternal(syntax);
		if (nameResult == null) {
			return null;
		}

		final var region = knownRegions.get(nameResult.getValue());
		if (region == null) {
			throw new IllegalArgumentException("unknown region: " + nameResult.getValue());
		}
		return new Result<>(nameResult.getOffset(), region);
	}

	private Result<String> parseIdentifierInternal(final String syntax) {
		final var matcher = IDENTIFIER_REGEX.matcher(syntax);
		if (matcher.matches()) {
			final String id = matcher.group(1);
			final int newOffset = matcher.end(1);
			return new Result<>(newOffset, id);
		}

		return null;
	}

	private Result<Region<P>> parseRegionLiteralInternal(final String syntax) {
		final var matcher = REGION_LITERAL_REGEX.matcher(syntax);
		if (!matcher.matches()) {
			return null;
		}

		final Set<P> places = new HashSet<>();
		String content = matcher.group(1);
		int offset = matcher.start(1);

		int comma = -1;
		do {
			content = content.substring(comma + 1);

			final var placeResult = parsePlaceInternal(content);
			if (placeResult == null) {
				throw parseError("region literal", syntax);
			}
			places.add(placeResult.getValue());
			comma = content.indexOf(',', placeResult.getOffset());
			offset += comma + 1;
		} while (comma > 0);

		offset = syntax.indexOf('}', offset) + 1;
		return new Result<>(offset, new Region<>(ImmutableSet.of(places)));
	}

	private Result<P> parsePlaceInternal(final String syntax) {
		final var quotedMatcher = QUOTED_PLACE_REGEX.matcher(syntax);
		if (quotedMatcher.matches()) {
			final String placeString = quotedMatcher.group(1);
			final int newOffset = quotedMatcher.end(1) + 1;
			final var place = mParsePlaceName.apply(placeString);
			assert place != null : "could not parse place name: " + placeString;
			return new Result<>(newOffset, place);
		}

		final var unquotedMatcher = IDENTIFIER_REGEX.matcher(syntax);
		if (unquotedMatcher.matches()) {
			final String placeString = unquotedMatcher.group(1);
			final int newOffset = unquotedMatcher.end(1);
			final var place = mParsePlaceName.apply(placeString);
			assert place != null : "could not parse place name: " + placeString;
			return new Result<>(newOffset, place);
		}

		return null;
	}

	private static RuntimeException parseError(final String thing, final String syntax) {
		return new IllegalArgumentException("Cannot parse as " + thing + ": " + syntax);
	}

	private static final class Result<X> {
		private final int mOffset;
		private final X mValue;

		private Result(final int offset, final X value) {
			mOffset = offset;
			mValue = value;
		}

		public int getOffset() {
			return mOffset;
		}

		public X getValue() {
			return mValue;
		}
	}
}
