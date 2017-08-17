package util;

public class PairXY<X, Y> implements IPair<X, Y> {
	
	private X x;
	private Y y;
	
	public PairXY(X x, Y y) {
		this.x = x;
		this.y = y;
	}

	@Override
	public X getFstElement() {
		// TODO Auto-generated method stub
		return x;
	}

	@Override
	public Y getSndElement() {
		// TODO Auto-generated method stub
		return y;
	}
	
	@Override
	public boolean equals(Object o) {
		if(! (o instanceof IPair)) return false;
		PairXY<X, Y> other = (PairXY<X, Y>)o;
		return x.equals(other.x)
			&& y.equals(other.y);
	}
	
	@Override
    public int hashCode(){
      return x.hashCode() + 31*y.hashCode();
    }	

}