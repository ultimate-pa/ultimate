package local.stalin.smt.theory.linar;

/**
 * This represents an entry in our sparse matrix.  The entries
 * are doubly linked 2d-shaped list, i.e. each entry knows its
 * row and its column predecessor.  The row lists are sorted, 
 * the column lists are randomly ordered and not consistently 
 * ordered with respect to other column lists.
 * 
 * TODO: Evaluate if a singly linked list is enough, at least 
 * for the column lists.
 * TODO: Maybe a mix between linked list and tree may be
 * faster if rows grow big, but pivoted rows are small.
 * 
 * @author Jochen Hoenicke
 */
public class MatrixEntry {
	Rational coeff;
	LinVar   row;
	LinVar   column;
	
	MatrixEntry prevInRow;
	MatrixEntry nextInRow;
	MatrixEntry prevInCol;
	MatrixEntry nextInCol;
	
	/**
	 * Insert a column variable into a row at its sorted position.
	 * @param nb  the column (non-basic) variable.
	 * @param value the coefficient in the matrix.
	 */
	public void insertRow(LinVar nb, Rational value) {
		assert(!value.equals(Rational.ZERO));
		MatrixEntry ptr = this.nextInRow;
		while (ptr.column.compareTo(nb) < 0)
			ptr = ptr.nextInRow;
		if (ptr.column == nb) {
			/* Add to existing entry */
			ptr.coeff = ptr.coeff.add(value);
			if (ptr.coeff.equals(Rational.ZERO))
				ptr.removeFromMatrix();
		} else {
			ptr.insertBefore(nb, value);
		}
	}
	
	/**
	 * Insert a column variable into a row before the current
	 * position.
	 * @param nb  the column (non-basic) variable.
	 * @param value the coefficient in the matrix.
	 */
	public void insertBefore(LinVar col, Rational value) {
		assert col.compareTo(this.column) < 0
		    && (this.prevInRow.column.compareTo(col) < 0
		    	|| this.prevInRow.column == LinVar.dummylinvar)
		    && !value.equals(Rational.ZERO);
		
		/* Create new entry before this */
		MatrixEntry newEntry = new MatrixEntry();
		newEntry.column = col;
		newEntry.row = this.row;
		newEntry.coeff = value;
		newEntry.nextInRow = this;
		newEntry.prevInRow = this.prevInRow;
		newEntry.nextInCol = col.headEntry.nextInCol;
		newEntry.prevInCol = col.headEntry;
		this.prevInRow.nextInRow = newEntry;
		this.prevInRow = newEntry;
		col.headEntry.nextInCol.prevInCol = newEntry;
		col.headEntry.nextInCol = newEntry;
	}

	public void removeFromRow() {
		prevInRow.nextInRow = nextInRow;
		nextInRow.prevInRow = prevInRow;
	}

	public void removeFromMatrix() {
		prevInRow.nextInRow = nextInRow;
		nextInRow.prevInRow = prevInRow;
		prevInCol.nextInCol = nextInCol;
		nextInCol.prevInCol = prevInCol;
	}

	public void add(Rational coeff, MatrixEntry other) {
		MatrixEntry trow = nextInRow;
		MatrixEntry orow = other.nextInRow;
		while (orow != other) {
			while (trow.column
					.compareTo(orow.column) < 0)
				trow = trow.nextInRow;
			Rational val = coeff.mul(orow.coeff);
			assert(!val.equals(Rational.ZERO));
			if (trow.column == orow.column) {
				Rational oldval = trow.coeff;
				trow.coeff = oldval.add(val);
				if (trow.coeff.equals(Rational.ZERO)) {
					trow.removeFromMatrix();
					if (oldval.isNegative()) {
						if( trow.column.upperassert == null )
							--trow.row.numlower;
						if( trow.column.lowerassert == null )
							--trow.row.numupper;
					} else {
						if( trow.column.upperassert == null )
							--trow.row.numupper;
						if( trow.column.lowerassert == null )
							--trow.row.numlower;
					}
				} else if (oldval.signum() != trow.coeff.signum()
						   && trow.column.isUBoundSet()
						   != trow.column.isLBoundSet()) {
					if (oldval.isNegative()
						^ trow.column.isLBoundSet()) {
						trow.row.numupper--;
						trow.row.numlower++;
					} else {
						trow.row.numlower--;
						trow.row.numupper++;
					}
				}
				trow = trow.nextInRow;
			} else {
				trow.insertBefore(orow.column, val);
				if (val.isNegative()) {
					if( orow.column.upperassert == null )
						++trow.row.numlower;
					if( orow.column.lowerassert == null )
						++trow.row.numupper;
				} else {
					if( orow.column.upperassert == null )
						++trow.row.numupper;
					if( orow.column.lowerassert == null )
						++trow.row.numlower;
				}
			}
			orow = orow.nextInRow;
		}
	}
	
	public String rowToString() {
		StringBuilder sb = new StringBuilder("[");
		String comma = "";
		for (MatrixEntry ptr = nextInRow; 
			ptr != this; ptr = ptr.nextInRow) {
			sb.append(comma);
			sb.append(ptr.coeff).append("*(").append(ptr.column).append(")");
			comma = ",";
		}
		return sb.append("]").toString();
	}
	
	public String colToString() {
		StringBuilder sb = new StringBuilder("[");
		String comma = "";
		for (MatrixEntry ptr = nextInCol; 
			ptr != this; ptr = ptr.nextInCol) {
			sb.append(comma);
			sb.append("(").append(ptr.row).append(")->").append(ptr.coeff);
			comma = ",";
		}
		return sb.append("]").toString();
	}
	
	public String toString() {
		if (nextInRow == null)
			return column+":"+colToString();
		if (nextInCol == null)
			return row+":"+rowToString();
		return "["+row+"/"+column+"]->"+coeff;
	}
}
