package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;

final class Tid {
    final private Integer[] value;
    final private String representation;

    Tid(Integer[] value) {
        this.value = value;
        representation = Tid.getRepresentation(value);
    }

    Tid(Expression[] expressions) {
        this(Arrays.stream(expressions)
			.map(
				x -> {
					if (!(x instanceof IntegerLiteral)) {
						// not allow TODO Throw error
					}
					
					return Integer.parseInt(((IntegerLiteral)x).getValue());
				}
			).toArray(Integer[]::new));
    }

    static String getRepresentation(Integer[] value) {

        StringBuilder sb = new StringBuilder("tid");

        for (Integer i : value) {
			sb.append("_").append(i);
		}

        return sb.toString();
    }

    Integer[] getValue() {
        return value;
    }

    @Override
    public String toString() {
        return representation;
    }

    @Override
    public boolean equals(Object o) {
        return Arrays.equals(value, ((Tid)o).value);
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(value);
    }
}