package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.typechecker.ITypeErrorReporter;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

class TypeErrorReporter implements ITypeErrorReporter<ILocation> {

	ILocation mLocation;

	public TypeErrorReporter(final ILocation location) {
		mLocation = location;
	}

	@Override
	public void report(final Function<ILocation, String> func) {
		throw new TypeCheckException(func.apply(mLocation));
	}
}