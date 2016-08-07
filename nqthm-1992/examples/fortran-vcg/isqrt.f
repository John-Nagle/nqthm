C     This is a test of the isqrt routine.  We compute the square root of
C     30.
C     To run this on a bsd unix and see the answer, which is 5, you incant
C     % f77 isqrt.f
C     % a.out
C     % cat fort.23      
      I = ISQRT(30)
      WRITE (23,17) I
17    FORMAT (I10.10)
      END
      INTEGER FUNCTION ISQRT(I)
      INTEGER I
C     CALCULATE THE SQUARE ROOT OF I USING THE NEWTON METHOD. 
      IF ((I .LT. 0)) STOP
      IF ((I .GT. 1)) GOTO 100
      ISQRT = I
      RETURN
C     ISQRT TAKES ON INCREASINGLY SMALLER VALUES AND CONVERGES TO THE SQ
C     UARE ROOT OF I. THE FIRST APPROXIMATION IS ONE HALF I, WHICH IS NO
C     T LESS THAN THE SQUARE ROOT OF I WHEN 1 IS LESS THAN I. 
100   ISQRT = (I / 2)
200   CONTINUE
C     ASSERTION LP
      IF (((I / ISQRT) .GE. ISQRT)) RETURN
      ISQRT = ((ISQRT + (I / ISQRT)) / 2)
C     XXX SQ-REWRITE-OFF-AGAIN
      GOTO 200
      END
