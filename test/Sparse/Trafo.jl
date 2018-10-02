@testset "Trafo" begin
  A = matrix(FlintZZ, [0 1 0 0 0;
                       0 0 2 0 0;
                       0 0 3 0 0;
                       0 0 0 4 0;
                       5 0 0 0 0])
  Asparse = sparse_matrix(A)

  T = @inferred sparse_trafo_scale(2, fmpz(-2))

  @inferred Hecke.apply_left!(Asparse, T)

  @test Asparse == sparse_matrix(fmpz[0 1 0 0 0;
                                      0 0 -4 0 0;
                                      0 0 3 0 0;
                                      0 0 0 4 0;
                                      5 0 0 0 0])
end
