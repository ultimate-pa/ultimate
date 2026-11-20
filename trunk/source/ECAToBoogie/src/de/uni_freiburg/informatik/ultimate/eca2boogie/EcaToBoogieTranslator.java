package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;

/** Placeholder for translating a checked ECA AST into a Boogie unit. */
public final class EcaToBoogieTranslator {
	private final EcaFile mFile;

	public EcaToBoogieTranslator(final EcaFile file) {
		mFile = Objects.requireNonNull(file);
	}

	public Unit getUnit() {
		// Translation of mFile is not implemented yet.
		return null;
	}
}
