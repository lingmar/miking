open Ustring.Op

module Mseq = struct
  type 'a t = 'a array Rope.t

  let create = Rope.create_array

  let empty = Rope.empty_array

  let length = Rope.length_array

  let concat = Rope.concat_array

  let get = Rope.get_array

  let set = Rope.set_array

  let cons = Rope.cons_array

  let snoc = Rope.snoc_array

  let reverse = Rope.reverse_array

  let split_at = Rope.split_at_array

  let subsequence = Rope.sub_array

  module Helpers = struct
    let of_list = Rope.Convert.of_list_array

    let to_list = Rope.Convert.to_list_array

    let of_array = Rope.Convert.of_array_array

    let to_array = Rope.Convert.to_array_array

    let of_ustring = Rope.Convert.of_ustring_array

    let to_ustring = Rope.Convert.to_ustring_array

    let equal = Rope.equal_array

    let map = Rope.map_array_array

    let fold_right = Rope.foldr_array

    let combine = Rope.combine_array_array

    let fold_right2 = Rope.foldr2_array
  end
end

module T = struct
  type 'a t =
    | Int of (int, Tensor.Num.int_elt) Tensor.Num.t
    | Float of (float, Tensor.Num.float_elt) Tensor.Num.t
    | NoNum of 'a Tensor.NoNum.t

  let int t = Int t

  let float t = Float t

  let no_num t = NoNum t
end

module Symb = struct
  type t = int

  let symid = ref 0

  let gensym _ =
    symid := !symid + 1 ;
    !symid

  let eqsym l r = l = r

  let hash s = s

  module Helpers = struct
    let nosym = -1

    let ustring_of_sym = ustring_of_int

    let string_of_sym s = Ustring.to_utf8 (ustring_of_sym s)
  end
end

module File = struct
  let read f = f |> Ustring.to_utf8 |> Ustring.read_file

  let write f d = Ustring.write_file (Ustring.to_utf8 f) d

  let exists f = f |> Ustring.to_utf8 |> Sys.file_exists

  let delete f = f |> Ustring.to_utf8 |> Sys.remove
end

module FloatConversion = struct
  let floorfi f = f |> Float.floor |> int_of_float

  let ceilfi f = f |> Float.ceil |> int_of_float

  let roundfi f = f |> Float.round |> int_of_float

  let string2float s =
    s |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Float.of_string
end

module IO = struct
  let print s = s |> Mseq.Helpers.to_ustring |> uprint_string

  let read_line _ =
    let line = try read_line () with End_of_file -> "" in
    line |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array
end

module RNG = struct
  let is_seeded = ref false

  let set_seed seed =
    Random.init seed ;
    is_seeded := true

  let int_u lower upper =
    if !is_seeded then ()
    else (
      Random.self_init () ;
      is_seeded := true ) ;
    lower + Random.int (upper - lower)
end

module MSys = struct
  exception Error of ustring

  let exit = exit

  let error m = raise (Error (Mseq.Helpers.to_ustring m))

  let argv =
    Sys.argv |> Mseq.Helpers.of_array
    |> Mseq.Helpers.map (fun a ->
           a |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array )
end

module Time = struct
  let get_wall_time_ms _ = Unix.gettimeofday () *. 1000.

  let sleep_ms ms = Thread.delay (float_of_int ms /. 1000.)
end

module Mmap = struct
  let empty cmp =
    let cmp x y = cmp (Obj.obj x) (Obj.obj y) in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.empty, cmp)

  let insert k v mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.add (Obj.repr k) v m, cmp)

  let remove k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.remove (Obj.repr k) m, cmp)

  let find k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.find (Obj.repr k) m

  let find_or_else f k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with Some v -> v | None -> f ()

  let find_apply_or_else f felse k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with
    | Some v ->
        f v
    | None ->
        felse ()

  let bindings mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    let binds = MapModule.bindings m in
    List.map (fun (k, v) -> (Obj.obj k, v)) binds

  let size mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.cardinal m

  let mem k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.mem (Obj.repr k) m

  let any p mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.exists (fun k v -> p (Obj.obj k) v) m

  let map f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.map f m, cmp)

  let map_with_key f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.mapi (fun k v -> f (Obj.obj k) v) m, cmp)

  let fold_with_key f z mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.fold (fun k v acc -> f (Obj.obj k) v acc) m z

  let eq veq m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.equal veq m1 m2

  let cmp vcmp m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.compare vcmp m1 m2

  let get_cmp_fun mCmpPair =
    let _, cmp = Obj.obj mCmpPair in
    fun x y -> Obj.repr (cmp x y)
end
