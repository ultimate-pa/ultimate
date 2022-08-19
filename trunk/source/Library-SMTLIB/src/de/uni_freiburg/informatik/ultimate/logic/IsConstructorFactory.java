package de.uni_freiburg.informatik.ultimate.logic;

public class IsConstructorFactory extends FunctionSymbolFactory {

	public IsConstructorFactory() {
		super(SMTLIBConstants.IS);
	}


	@Override
	public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
		if (indices.length != 1 || paramSorts.length != 1) {
			return null;
		}

		if (!paramSorts[0].getSortSymbol().isDatatype()) {
			return null;
		}

		final DataType datatype = (DataType) paramSorts[0].getSortSymbol();
		for (int i = 0; i < datatype.getConstructors().length; i++) {
			if (indices[0].equals(datatype.getConstructors()[i].getName())) {
				return paramSorts[0].getTheory().getBooleanSort();
			}
		}
		return null;
	}
}
