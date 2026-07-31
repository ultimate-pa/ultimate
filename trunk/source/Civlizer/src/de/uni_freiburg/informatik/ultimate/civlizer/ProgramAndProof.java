/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * Internal container that bundles together the Boogie AST, the generated ICFG, and the associated proof information.
 *
 * <p>
 * It also computes derived structures such as ghost update mappings and annotation maps extracted from the ICFC and
 * witness annotations.
 * </p>
 */
final class ProgramAndProof {

	private Unit mBoogieAst = null;
	private BoogieIcfgContainer mIcfg = null;
	private List<OwickiGriesAnnotation> mProof = null;
	private Map<ILocation, Set<CallStatement>> mGhostUpdateMap = null;
	private Map<ILocation, Expression> mAnnotationMap = null;
	private ThreadTemplateVisitor mTemplateVisitor = null;

	ProgramAndProof() {
	}

	ThreadTemplateVisitor getTemplateVisitor() {
		return mTemplateVisitor;
	}

	BoogieIcfgContainer getIcfg() {
		return mIcfg;
	}

	Unit getBoogieAst() {
		return mBoogieAst;
	}

	List<OwickiGriesAnnotation> getProof() {
		return mProof;
	}

	void setBoogieAst(final Unit boogieAst) {
		mBoogieAst = boogieAst;
	}

	void setIcfg(final BoogieIcfgContainer icfg) {
		mIcfg = icfg;
	}

	void setProof(final List<OwickiGriesAnnotation> proof) {
		mProof = proof;
	}

	boolean isFull() {
		return mBoogieAst != null && mIcfg != null && mProof != null;
	}

	Map<ILocation, Set<CallStatement>> getGhostUpdateMap() {
		return mGhostUpdateMap;
	}

	/**
	 * Preprocesses the ICFC to extract ghost updates and initialize auxiliary structures.
	 *
	 * <p>
	 * This method:
	 * <ul>
	 * <li>Initializes the thread template visitor</li>
	 * <li>Scans all CFG edges for {@link WitnessGhostUpdate} annotations</li>
	 * <li>Creates Boogie call statements representing ghost updates</li>
	 * <li>Stores them in {@code mGhostUpdateMap}</li>
	 * </ul>
	 * </p>
	 */
	/**
	 * Preprocesses the ICFC by initializing auxiliary structures and extracting ghost updates from CFG edges.
	 */
	void preprocess() {
		mTemplateVisitor = new ThreadTemplateVisitor(mBoogieAst, mIcfg);
		mGhostUpdateMap = new HashMap<>();

		computeAnnotationMap();

		for (final BoogieIcfgLocation location : getProgramLocations()) {
			processGhostUpdates(location);
		}
	}

	private Collection<BoogieIcfgLocation> getProgramLocations() {
		final Collection<BoogieIcfgLocation> locations = new ArrayList<>();

		for (final Map<?, BoogieIcfgLocation> programPoint : mIcfg.getProgramPoints().values()) {
			locations.addAll(programPoint.values());
		}

		return locations;
	}

	private void processGhostUpdates(final BoogieIcfgLocation location) {
		for (final var edge : location.getOutgoingEdges()) {
			final WitnessGhostUpdate ghostUpdate = WitnessGhostUpdate.getAnnotation(edge);

			if (ghostUpdate == null) {
				continue;
			}

			final ILocation updateLocation = ILocation.getAnnotation(edge);

			if (updateLocation == null) {
				continue;
			}

			final Set<CallStatement> assignments =
					createGhostUpdateAssignments(updateLocation, ghostUpdate.getUpdate());

			mGhostUpdateMap.put(updateLocation, assignments);
		}
	}

	private Set<CallStatement> createGhostUpdateAssignments(final ILocation location, final Map<?, ?> updates) {

		final Set<CallStatement> assignments = new HashSet<>();

		for (final Map.Entry<?, ?> update : updates.entrySet()) {
			assignments.add(
					createGhostUpdateAssignment(location, update.getKey().toString(), (Expression) update.getValue()));
		}

		return assignments;
	}

	private CallStatement createGhostUpdateAssignment(final ILocation location, final String variableName,
			final Expression value) {

		final IntegerLiteral layerNum = new IntegerLiteral(location, "2");

		return new CallStatement(location,
				new NamedAttribute[] { new NamedAttribute(location, "layer", new Expression[] { layerNum }) }, false,
				new VariableLHS[] { new VariableLHS(location, variableName) }, "Copy", new Expression[] { value });
	}

	private void computeAnnotationMap() {

		mAnnotationMap = new HashMap<>();

		for (final Declaration decl : mBoogieAst.getDeclarations()) {
			if (decl instanceof final Procedure proc) {
				for (final BoogieIcfgLocation loc : mIcfg.getProgramPoints().get(proc.getIdentifier()).values()) {

					final var codeLocation = ILocation.getAnnotation(loc);

					if (!loc.isErrorLocation() && loc.getBoogieASTNode() instanceof Statement) {

						final Expression invariant = (WitnessInvariant.getAnnotation(loc) != null)
								? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant()
								: null;

						// merge together
						if (mAnnotationMap.get(codeLocation) != null) {
							final Expression buf = mAnnotationMap.get(codeLocation);
							mAnnotationMap.put(codeLocation, new BinaryExpression(codeLocation,
									BinaryExpression.Operator.LOGICAND, invariant, buf));
						} else {
							mAnnotationMap.put(codeLocation, invariant);
						}
					}
				}
			}
		}
	}

	Map<ILocation, Expression> getAnnotationMap() {
		return mAnnotationMap;
	}
}