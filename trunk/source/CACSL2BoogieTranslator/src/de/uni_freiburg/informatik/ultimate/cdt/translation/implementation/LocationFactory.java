/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
/**
 * Location in a C+ACSL program.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.LineDirectiveMapping;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class LocationFactory {

	private final LineDirectiveMapping mLineDirectiveMapping;

	public LocationFactory(final LineDirectiveMapping lineDirectiveMapping) {
		mLineDirectiveMapping = lineDirectiveMapping;
	}

	public ILocation createRootCLocation(final Set<IASTTranslationUnit> set) {
		return new CACSLProjectLocation(set);
	}

	public CACSLLocation createCLocation(final IASTNode cNode) {
		return new CLocation(cNode, new Check(Check.Spec.UNKNOWN), false, mLineDirectiveMapping);
	}

	public static CACSLLocation createIgnoreCLocation(final IASTNode cNode) {
		return new CLocation(cNode, new Check(Check.Spec.UNKNOWN), true, null);
	}

	public static CACSLLocation createIgnoreCLocation() {
		return new CLocation(null, new Check(Check.Spec.UNKNOWN), true, null);
	}

	public CACSLLocation createACSLLocation(final ACSLNode acslNode) {
		return new ACSLLocation(acslNode, new Check(Check.Spec.UNKNOWN), false);
	}

	public CACSLLocation createACSLLocation(final ACSLNode acslNode, final Check type) {
		return new ACSLLocation(acslNode, type, false);
	}

	public CACSLLocation createCLocation(final IASTNode cNode, final Check type) {
		return new CLocation(cNode, type, false, mLineDirectiveMapping);
	}

	public static CACSLLocation createLocation(final CACSLLocation loc) {
		if (loc instanceof ACSLLocation) {
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation(),
					realLoc.getLineDirectiveMapping());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public static CACSLLocation createLocation(final CACSLLocation loc, final Check type) {
		if (loc instanceof ACSLLocation) {
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation(),
					realLoc.getLineDirectiveMapping());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public static CACSLLocation createIgnoreLocation(final ILocation loc) {
		if (loc instanceof ACSLLocation) {
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), realLoc.getCheck(), true);
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), realLoc.getCheck(), true, realLoc.getLineDirectiveMapping());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * A {@link CACSLLocation} that represents a whole project.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class CACSLProjectLocation extends DefaultLocation {
		private static final long serialVersionUID = -7960532970979883689L;
		private final Set<String> mFilenames;

		public CACSLProjectLocation(final Set<IASTTranslationUnit> set) {
			super(Objects.requireNonNull(set).stream().findAny()
					.orElseThrow(() -> new IllegalArgumentException("set is empty")).getFilePath(), -1, -1, -1, -1);
			mFilenames =
					Collections.unmodifiableSet(set.stream().map(a -> a.getFilePath()).collect(Collectors.toSet()));
		}

		public Set<String> getFilenames() {
			return mFilenames;
		}
		
		@Override
		public IAnnotations merge(final IAnnotations other) {
			if (other == null) {
				return this;
			}
			if (other == this) {
				return this;
			}
			return super.merge(other);
		}

	}
}
