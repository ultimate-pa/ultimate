package de.uni_freiburg.informatik.ultimate.lib.pea.util;

import java.util.Objects;

public class SimplePair<F, S> {
    private final F first;
    private final S second;

    public SimplePair(F first, S second) {
        this.first = first;
        this.second = second;
    }

    public F getFirst() {
        return first;
    }

    public S getSecond() {
        return second;
    }
    
    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof SimplePair<?, ?>)) {
            return false;
        }
        SimplePair<?, ?> other = (SimplePair<?, ?>) obj;
        return Objects.equals(first, other.first) && Objects.equals(second, other.second);
    }
    
    @Override
    public String toString() {
        String firstString = (first != null) ? first.toString() : "null";
        String secondString = (second != null) ? second.toString() : "null";
        return "(" + firstString + ", " + secondString + ")";
    }
}