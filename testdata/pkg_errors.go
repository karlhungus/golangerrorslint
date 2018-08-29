// Test for naming errors.

package foo

import (
	"github.com/pkg/errors"
)

var errFoo = errors.New("test")
var unexp = errors.Wrap(errFoo, "some unexported error") // MATCH /error var.*unexp.*errFoo/

// Exp ...
var Exp = errors.Wrap(errFoo, "some exported error") // MATCH /error var.*Exp.*ErrFoo/

var (
	e1 = errors.Wrapf(errFoo, "blah %d", 4) // MATCH /error var.*e1.*errFoo/
	// E2 ...
	E2 = errors.Wrapf(errFoo, "blah %d", 5) // MATCH /error var.*E2.*ErrFoo/
)

func f() {
	var whatever = errors.Wrapf(errFoo, "ok") // ok
	_ = whatever
}

// Check for the error strings themselves.

func g(x int) error {
	var err error
	src := errors.New("some error")
	err = errors.Wrapf(src, "This %d is too low", x)     // MATCH /error strings.*be capitalized/
	err = errors.Wrapf(src, "XML time")                  // ok
	err = errors.Wrapf(src, "newlines are fun\n")        // MATCH /error strings.*end with punctuation/
	err = errors.Wrapf(src, "Newlines are really fun\n") // MATCH /error strings.+not be capitalized/
	err = errors.New(`too much stuff.`)                  // MATCH /error strings.*end with punctuation/
	err = errors.New("This is too low")                  // MATCH /error strings.*be capitalized/
	err = errors.Wrap(src, `too much stuff.`)            // MATCH /error strings.*end with punctuation/
	err = errors.Wrap(src, "This %d is too low", x)      // MATCH /error strings.*be capitalized/
	return err
}
