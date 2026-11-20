package de.uni_freiburg.informatik.ultimate.eca2boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;

/** Receives the parsed ECA file and hands it to the translator. */
public final class EcaToBoogieObserver extends BaseObserver {
	private Unit mUnit;

	@Override
	public boolean process(final IElement root) {
		if (root instanceof final ObjectContainer<?> container && container.getValue() instanceof final EcaFile file) {
			mUnit = new EcaToBoogieTranslator(file).getUnit();
		}
		return false;
	}

	public Unit getUnit() {
		return mUnit;
	}
}
