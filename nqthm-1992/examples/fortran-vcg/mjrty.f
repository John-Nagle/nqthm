C     This is a test of the mjrty FORTRAN program.  We look for
C     and detect a majority in the sequence (1,2,1,5,1).
C     To run this on a bsd unix and see the answer, which is 1 and 1, you incant
C     % f77 mjrty.f
C     % a.out
C     % cat fort.23      
      INTEGER I(5)
      LOGICAL BOOLE
      INTEGER CAND
      I(1) = 1
      I(2) = 2
      I(3) = 1
      I(4) = 5
      I(5) = 1
      CALL MJRTY(I,5,BOOLE,CAND)
      WRITE (23, 17) BOOLE, CAND
 17   FORMAT (B, I10.10)
      END
      SUBROUTINE MJRTY(A, N, BOOLE, CAND)
      INTEGER N
      INTEGER A
      LOGICAL BOOLE
      INTEGER CAND
      INTEGER I
      INTEGER K
      DIMENSION A(N)
      K = 0
C     THE FOLLOWING DO IMPLEMENTS THE PAIRING PHASE. CAND IS THE CURRENT
C     LY LEADING CANDIDATE AND K IS THE NUMBER OF UNPAIRED VOTES FOR CAN
C     D. 
      DO 100 I = 1, N
C     DOJUNK PHASE1-HINT
      IF ((K .EQ. 0)) GOTO 50
      IF ((CAND .EQ. A(I))) GOTO 75
      K = (K - 1)
      GOTO 100
50    CAND = A(I)
      K = 1
C     XXX PHASE1-INVRT-F-T
      GOTO 100
75    K = (K + 1)
100   CONTINUE
      IF ((K .EQ. 0)) GOTO 300
      BOOLE = .TRUE.
      IF ((K .GT. (N / 2))) RETURN
C     WE NOW ENTER THE COUNTING PHASE. BOOLE IS SET TO TRUE IN ANTICIPAT
C     ION OF FINDING CAND IN THE MAJORITY. K IS USED AS THE RUNNING TALL
C     Y FOR CAND. WE EXIT AS SOON AS K EXCEEDS N/2. 
      K = 0
      DO 200 I = 1, N
C     DOJUNK PHASE2
      IF ((CAND .NE. A(I))) GOTO 200
      K = (K + 1)
C     XXX OUTPUT-HINT
      IF ((K .GT. (N / 2))) RETURN
200   CONTINUE
300   BOOLE = .FALSE.
C     XXX HINT-FOR-PHASE1-INVRT-T-T
C     XXX HINT-FOR-PHASE2-INVRT-T
      RETURN
      END
