/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtcomp;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This script does the main work of the preparation. It also checks for compliance with the rules of SMT-COMP 2012.
 *
 * @author Juergen Christ
 */
public class PrepareScript extends LoggingScript {

	private final Track mTrack;

	public PrepareScript(final Track track, final String file) throws FileNotFoundException {
		super(file, false);
		mTrack = track;
		if (track.hasInitalOption()) {
			setOption(track.getInitialOption(), track.getInitialOptionValue());
		}
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		if (arity != 0) {
			throw new IllegalArgumentException("Sorts with non-0 arity not allowed in SMTCOMP");
		}
		super.declareSort(sort, arity);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		if (!mTrack.isPushPopAllowed()) {
			throw new IllegalArgumentException("push not allowed in this track");
		}
		if (levels != 1) {
			throw new IllegalArgumentException("Only (push 1) allowed");
		}
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		if (!mTrack.isPushPopAllowed()) {
			throw new IllegalArgumentException("pop not allowed in this track");
		}
		if (levels != 1) {
			throw new IllegalArgumentException("Only (pop 1) allowed");
		}
		super.pop(levels);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		// Do nothing since no track allows this command
		return new Term[0];
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		if (mTrack == Track.PROOF_GEN) {
			return super.getProof();
		}
		// Do nothing since command not allowed in this track
		throw new UnsupportedOperationException("Not allowed in this trace");
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		if (mTrack == Track.UNSAT_CORE) {
			return super.getUnsatCore();
		}
		// Do nothing since command not allowed in this track
		return new Term[0];
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		// Do nothing since no track allows this command
		return Collections.emptyMap();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		// Do nothing since no track allows this command
		final Map<String, Boolean> empty = Collections.emptyMap();
		return new Assignments(empty);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		// Do nothing since no track allows this command
		return term;
	}

	@Override
	public void reset() {
		throw new AssertionError("What?");
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		// Do nothing since no track allows this command
		return new Term[0];
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		// By default, I allow :pattern
		final List<Annotation> allowed = new ArrayList<>();
		for (final Annotation annot : annotations) {
			if (annot.getKey().equals(":pattern")) {
				allowed.add(annot);
			} else if (mTrack.isNamedAllowed() && annot.getKey().equals(":named")) {
				allowed.add(annot);
				// All other annotations are silently discarded...
			}
		}
		return super.annotate(t, allowed.toArray(new Annotation[allowed.size()]));
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		// Do nothing since no track allows this command
		return new Model() {

			@Override
			public Term evaluate(final Term input) {
				return input;
			}

			@Override
			public Map<Term, Term> evaluate(final Term[] input) {
				return Collections.emptyMap();
			}

			@Override
			public Set<FunctionSymbol> getDefinedFunctions() {
				return Collections.emptySet();
			}

			@Override
			public Term getFunctionDefinition(final String func, final TermVariable[] args) {
				return null;
			}
		};
	}
}
